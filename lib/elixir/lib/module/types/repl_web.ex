# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

defmodule Module.Types.Repl.Web do
  @moduledoc false

  alias Module.Types.Repl

  @default_port 4100
  @max_body_size 1_000_000

  def start_link(opts \\ []) do
    port = Keyword.get(opts, :port, @default_port)

    with {:ok, states} <- Agent.start(fn -> %{} end),
         {:ok, listen_socket, actual_port} <- listen(port) do
      pid = spawn(fn -> accept_loop(listen_socket, states) end)

      {:ok, %{pid: pid, port: actual_port, socket: listen_socket, states: states}}
    end
  end

  def stop(%{pid: pid, socket: socket, states: states}) do
    :gen_tcp.close(socket)

    if Process.alive?(pid) do
      Process.exit(pid, :normal)
    end

    if Process.alive?(states) do
      Agent.stop(states, :normal)
    end
  end

  def serve!(opts \\ []) do
    {:ok, server} = start_link(opts)

    IO.puts("Type REPL web UI running at http://127.0.0.1:#{server.port}")
    IO.puts("Press Ctrl+C twice to stop.")

    receive do
      :stop -> stop(server)
    end
  end

  defp listen(port) do
    opts = [:binary, packet: :raw, active: false, reuseaddr: true, ip: {127, 0, 0, 1}]

    case :gen_tcp.listen(port, opts) do
      {:ok, socket} ->
        {:ok, actual_port} = :inet.port(socket)
        {:ok, socket, actual_port}

      {:error, :eaddrinuse} when port != 0 ->
        listen(0)

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp accept_loop(listen_socket, states) do
    case :gen_tcp.accept(listen_socket) do
      {:ok, socket} ->
        spawn(fn -> handle_socket(socket, states) end)
        accept_loop(listen_socket, states)

      {:error, :closed} ->
        :ok

      {:error, _reason} ->
        accept_loop(listen_socket, states)
    end
  end

  defp handle_socket(socket, states) do
    case read_request(socket) do
      {:ok, request} ->
        respond(socket, route(request, states))

      {:error, :too_large} ->
        respond(socket, response(413, "text/plain; charset=utf-8", "Request too large"))

      {:error, _reason} ->
        respond(socket, response(400, "text/plain; charset=utf-8", "Bad request"))
    end
  after
    :gen_tcp.close(socket)
  end

  defp route(%{method: "GET", path: "/"}, _states) do
    response(200, "text/html; charset=utf-8", page())
  end

  defp route(%{method: "GET", path: "/favicon.ico"}, _states) do
    response(204, "text/plain; charset=utf-8", "")
  end

  defp route(%{method: "POST", path: "/api/eval", body: body}, states) do
    with {:ok, %{"session" => session, "input" => input}}
         when is_binary(session) and is_binary(input) <-
           JSON.decode(body) do
      result =
        Agent.get_and_update(states, fn states ->
          state = Map.get(states, session, Repl.new())

          case Repl.eval(input, state) do
            {:ok, output, state} ->
              reply = %{ok: true, output: output, aliases: aliases(state)}
              {reply, Map.put(states, session, state)}

            {:error, message, state} ->
              reply = %{ok: false, error: message, aliases: aliases(state)}
              {reply, Map.put(states, session, state)}
          end
        end)

      json(result)
    else
      _ -> json(%{ok: false, error: "invalid JSON request"}, 400)
    end
  end

  defp route(%{method: "POST", path: "/api/reset", body: body}, states) do
    with {:ok, %{"session" => session}} when is_binary(session) <- JSON.decode(body) do
      Agent.update(states, &Map.put(&1, session, Repl.new()))
      json(%{ok: true, output: [], aliases: []})
    else
      _ -> json(%{ok: false, error: "invalid JSON request"}, 400)
    end
  end

  defp route(%{path: path}, _states) do
    response(404, "text/plain; charset=utf-8", "No route for #{path}")
  end

  defp aliases(%Repl{aliases: aliases}) do
    aliases
    |> Map.keys()
    |> Enum.sort()
  end

  defp json(term, status \\ 200) do
    response(status, "application/json; charset=utf-8", JSON.encode!(term))
  end

  defp response(status, content_type, body) do
    body = IO.iodata_to_binary(body)
    reason = reason(status)

    headers = [
      "HTTP/1.1 #{status} #{reason}\r\n",
      "Content-Type: #{content_type}\r\n",
      "Content-Length: #{byte_size(body)}\r\n",
      "Cache-Control: no-store\r\n",
      "Connection: close\r\n",
      "\r\n"
    ]

    [headers, body]
  end

  defp respond(socket, body), do: :gen_tcp.send(socket, body)

  defp reason(200), do: "OK"
  defp reason(204), do: "No Content"
  defp reason(400), do: "Bad Request"
  defp reason(404), do: "Not Found"
  defp reason(413), do: "Payload Too Large"

  defp read_request(socket, buffer \\ "") do
    case :gen_tcp.recv(socket, 0, 5_000) do
      {:ok, data} ->
        buffer = buffer <> data

        case parse_request(buffer) do
          {:more, content_length} when content_length <= @max_body_size ->
            read_request(socket, buffer)

          {:more, _content_length} ->
            {:error, :too_large}

          result ->
            result
        end

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp parse_request(buffer) do
    case :binary.split(buffer, "\r\n\r\n") do
      [headers, body] ->
        content_length =
          headers
          |> headers_to_map()
          |> Map.get("content-length", "0")
          |> String.to_integer()

        if byte_size(body) < content_length do
          {:more, content_length}
        else
          [request_line | _] = String.split(headers, "\r\n")
          [method, path, _version] = String.split(request_line, " ", parts: 3)

          {:ok,
           %{
             method: method,
             path: normalize_path(path),
             body: binary_part(body, 0, content_length)
           }}
        end

      [_] ->
        {:more, 0}
    end
  rescue
    _ -> {:error, :invalid}
  end

  defp headers_to_map(headers) do
    headers
    |> String.split("\r\n")
    |> tl()
    |> Map.new(fn line ->
      [key, value] = String.split(line, ":", parts: 2)
      {String.downcase(key), String.trim(value)}
    end)
  end

  defp normalize_path(path) do
    path
    |> String.split("?", parts: 2)
    |> hd()
  end

  defp page do
    ~S"""
    <!doctype html>
    <html lang="en">
    <head>
      <meta charset="utf-8">
      <meta name="viewport" content="width=device-width, initial-scale=1">
      <title>Elixir Types REPL</title>
      <style>
        :root {
          color-scheme: light;
          --bg: #f4f5f1;
          --surface: #ffffff;
          --surface-strong: #fdfaf2;
          --ink: #172121;
          --muted: #64716f;
          --line: #d7ddd6;
          --teal: #0f766e;
          --teal-strong: #0b5f5a;
          --amber: #b45309;
          --violet: #5b4b8a;
          --red: #b42318;
          --code-bg: #18211f;
          --code-ink: #eaf2ec;
          --shadow: 0 18px 45px rgba(25, 35, 31, 0.10);
        }

        * {
          box-sizing: border-box;
        }

        body {
          margin: 0;
          min-height: 100vh;
          background: var(--bg);
          color: var(--ink);
          font: 15px/1.45 system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
        }

        button,
        textarea {
          font: inherit;
        }

        .shell {
          min-height: 100vh;
          display: grid;
          grid-template-rows: auto 1fr;
        }

        header {
          display: flex;
          align-items: center;
          justify-content: space-between;
          gap: 18px;
          padding: 18px clamp(16px, 3vw, 34px);
          border-bottom: 1px solid var(--line);
          background: rgba(255, 255, 255, 0.78);
          backdrop-filter: blur(12px);
        }

        h1 {
          margin: 0;
          font-size: clamp(20px, 3vw, 28px);
          font-weight: 720;
          letter-spacing: 0;
        }

        .status {
          display: flex;
          align-items: center;
          gap: 10px;
          color: var(--muted);
          font-size: 13px;
          white-space: nowrap;
        }

        .dot {
          width: 10px;
          height: 10px;
          border-radius: 50%;
          background: var(--amber);
          box-shadow: 0 0 0 4px rgba(180, 83, 9, 0.14);
        }

        .dot.ok {
          background: var(--teal);
          box-shadow: 0 0 0 4px rgba(15, 118, 110, 0.14);
        }

        main {
          display: grid;
          grid-template-columns: minmax(330px, 0.95fr) minmax(360px, 1.05fr);
          gap: 18px;
          padding: 18px clamp(16px, 3vw, 34px) 26px;
          min-height: 0;
        }

        .pane {
          min-width: 0;
          background: var(--surface);
          border: 1px solid var(--line);
          border-radius: 8px;
          box-shadow: var(--shadow);
          overflow: hidden;
          display: flex;
          flex-direction: column;
        }

        .pane-head {
          display: flex;
          align-items: center;
          justify-content: space-between;
          gap: 12px;
          padding: 13px 14px;
          border-bottom: 1px solid var(--line);
          background: var(--surface-strong);
        }

        .pane-title {
          font-weight: 700;
          font-size: 14px;
        }

        .actions {
          display: flex;
          align-items: center;
          gap: 8px;
          flex-wrap: wrap;
          justify-content: flex-end;
        }

        button {
          border: 1px solid var(--line);
          background: #fff;
          color: var(--ink);
          min-height: 36px;
          padding: 0 12px;
          border-radius: 7px;
          cursor: pointer;
        }

        button:hover {
          border-color: #aab8b4;
        }

        button:focus-visible,
        textarea:focus-visible {
          outline: 3px solid rgba(15, 118, 110, 0.2);
          outline-offset: 2px;
        }

        .primary {
          background: var(--teal);
          border-color: var(--teal);
          color: #fff;
          font-weight: 700;
        }

        .primary:hover {
          background: var(--teal-strong);
          border-color: var(--teal-strong);
        }

        .danger {
          color: var(--red);
        }

        textarea {
          width: 100%;
          min-height: 340px;
          flex: 1;
          resize: vertical;
          border: 0;
          padding: 16px;
          background: var(--code-bg);
          color: var(--code-ink);
          font: 14px/1.55 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
          letter-spacing: 0;
          tab-size: 2;
        }

        .examples {
          padding: 12px;
          display: grid;
          grid-template-columns: repeat(2, minmax(0, 1fr));
          gap: 8px;
          border-top: 1px solid var(--line);
          background: #fbfcfa;
        }

        .example {
          text-align: left;
          height: 42px;
          overflow: hidden;
          white-space: nowrap;
          text-overflow: ellipsis;
          font-size: 13px;
        }

        .right-stack {
          display: grid;
          grid-template-rows: minmax(260px, 1fr) auto auto;
          gap: 18px;
          min-height: 0;
        }

        .output {
          padding: 12px;
          overflow: auto;
          min-height: 300px;
        }

        .entry {
          border: 1px solid var(--line);
          border-radius: 8px;
          overflow: hidden;
          margin-bottom: 10px;
          background: #fff;
        }

        .entry:last-child {
          margin-bottom: 0;
        }

        .entry pre {
          margin: 0;
          padding: 12px;
          overflow: auto;
          font: 13px/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
          letter-spacing: 0;
        }

        .entry .cmd {
          background: #f6f8f6;
          color: #253330;
          border-bottom: 1px solid var(--line);
        }

        .entry .result {
          color: var(--teal-strong);
        }

        .entry .error {
          color: var(--red);
        }

        .empty {
          color: var(--muted);
          padding: 18px;
        }

        .alias-bar {
          padding: 12px;
          display: flex;
          gap: 8px;
          flex-wrap: wrap;
          min-height: 62px;
          align-content: flex-start;
        }

        .chip {
          display: inline-flex;
          align-items: center;
          min-height: 30px;
          padding: 0 10px;
          border: 1px solid rgba(91, 75, 138, 0.24);
          background: rgba(91, 75, 138, 0.08);
          color: var(--violet);
          border-radius: 999px;
          font-size: 13px;
          font-weight: 650;
        }

        .docs {
          padding: 12px 14px 14px;
          display: grid;
          gap: 10px;
        }

        .doc-row {
          display: grid;
          grid-template-columns: minmax(112px, 0.45fr) 1fr;
          gap: 12px;
          align-items: start;
          color: var(--muted);
          font-size: 13px;
          line-height: 1.45;
        }

        .doc-row > code {
          display: block;
          padding: 3px 6px;
          overflow-wrap: anywhere;
          border: 1px solid var(--line);
          border-radius: 6px;
          background: #f6f8f6;
          color: #1f2a27;
          font: 12px/1.4 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
          letter-spacing: 0;
        }

        .doc-row span code {
          padding: 1px 4px;
          border: 1px solid var(--line);
          border-radius: 5px;
          background: #f6f8f6;
          color: #1f2a27;
          font: 12px/1.4 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
          letter-spacing: 0;
        }

        .doc-note {
          color: var(--muted);
          font-size: 13px;
          line-height: 1.45;
        }

        .doc-note a {
          color: var(--violet);
          font-weight: 650;
          text-decoration: none;
        }

        .doc-note a:hover {
          text-decoration: underline;
        }

        @media (max-width: 860px) {
          header {
            align-items: flex-start;
            flex-direction: column;
          }

          main {
            grid-template-columns: 1fr;
          }

          .examples {
            grid-template-columns: 1fr;
          }

          .doc-row {
            grid-template-columns: 1fr;
            gap: 4px;
          }
        }

        @media (max-width: 520px) {
          .pane-head {
            align-items: flex-start;
            flex-direction: column;
          }

          .actions {
            width: 100%;
            justify-content: flex-start;
          }
        }
      </style>
    </head>
    <body>
      <div class="shell">
        <header>
          <h1>Elixir Types REPL</h1>
          <div class="status" aria-live="polite">
            <span id="dot" class="dot"></span>
            <span id="status">Ready</span>
          </div>
        </header>

        <main>
          <section class="pane">
            <div class="pane-head">
              <div class="pane-title">Input</div>
              <div class="actions">
                <button id="clearInput" type="button">Clear</button>
                <button id="run" type="button" class="primary" title="Run (Ctrl+Enter)">Run</button>
              </div>
            </div>
            <textarea id="input" spellcheck="false">type pair = {boolean(), boolean} ;;
    {false, true} <= pair ;;
    {integer, boolean} <= {integer, ...} ;;
    %{foo: term()} and %{..., foo: term(), bar: term()} ;;
    ((integer, integer) -> integer) (integer, integer) ;;
    %{foo: integer, bar: boolean}[:foo] ;;
    (integer() -> boolean -> integer()) integer boolean() ;;</textarea>
            <div class="examples" id="examples"></div>
          </section>

          <div class="right-stack">
            <section class="pane">
              <div class="pane-head">
                <div class="pane-title">Output</div>
                <div class="actions">
                  <button id="clearOutput" type="button">Clear</button>
                  <button id="reset" type="button" class="danger">Reset</button>
                </div>
              </div>
              <div id="output" class="output">
                <div class="empty">No results yet.</div>
              </div>
            </section>

            <section class="pane">
              <div class="pane-head">
                <div class="pane-title">Aliases</div>
              </div>
              <div id="aliases" class="alias-bar">
                <span class="chip">none</span>
              </div>
            </section>

            <section class="pane">
              <div class="pane-head">
                <div class="pane-title">Reference</div>
              </div>
              <div class="docs">
                <div class="doc-row">
                  <code>type a = t ;;</code>
                  <span>Defines an alias that persists for this browser session.</span>
                </div>
                <div class="doc-row">
                  <code>t ;;</code>
                  <span>Normalizes and prints a type.</span>
                </div>
                <div class="doc-row">
                  <code>a &lt;= b ;;</code>
                  <span>Tests subtyping. Use <code>a = b ;;</code> for semantic equality and <code>a &gt;= b ;;</code> for reverse subtyping.</span>
                </div>
                <div class="doc-row">
                  <code>a &lt;~ b ;;</code>
                  <span>Tests gradual precision. <code>a &lt;~= b</code> is accepted as the same relation.</span>
                </div>
                <div class="doc-row">
                  <code>a &lt;=~ b ;;</code>
                  <span>Tests consistent subtyping, defined as <code>lower(a) &lt;= upper(b)</code>.</span>
                </div>
                <div class="doc-row">
                  <code>a ~&lt;= b ;;</code>
                  <span>Tests Elixir compatibility from left to right.</span>
                </div>
                <div class="doc-row">
                  <code>t when a: bound ;;</code>
                  <span>Introduces local type variable <code>a</code>. A non-<code>term()</code> bound is applied as an intersection at each occurrence.</span>
                </div>
                <div class="doc-row">
                  <code>[a &lt;= b ; ...] ;;</code>
                  <span>Tallies subtype constraints and prints principal substitutions. Unknown lowercase identifiers inside brackets are type variables.</span>
                </div>
                <div class="doc-row">
                  <code>t s ;;</code>
                  <span>Applies function type <code>t</code> to argument type <code>s</code>. Define multi-arity functions with <code>(s1, s2 -&gt; ret)</code> and apply with <code>t (s1, s2) ;;</code>.</span>
                </div>
                <div class="doc-row">
                  <code>list(t, tail)</code>
                  <span>List aliases are <code>list()</code>, <code>list(t)</code>, and <code>list(t, tail)</code>; non-empty lists use <code>non_empty_list(t)</code> or <code>non_empty_list(t, tail)</code>.</span>
                </div>
                <div class="doc-row">
                  <code>t[s] ;;</code>
                  <span>Models Elixir <code>map[key]</code> access; the result includes <code>nil</code> when a key can be absent.</span>
                </div>
                <div class="doc-row">
                  <code>t.a ;;</code>
                  <span>Selects required map/record field <code>:a</code>; this errors when the field is absent or optional.</span>
                </div>
                <div class="doc-row">
                  <code>precise? head ;;</code>
                  <span>Checks pattern and guard precision, as in <code>precise? {x, y} when x == y ;;</code>.</span>
                </div>
                <div class="doc-row">
                  <code>a or b</code>
                  <span>Set union. Intersections and differences are <code>a and b</code>, <code>a and not b</code>, and <code>not a</code>.</span>
                </div>
                <div class="doc-row">
                  <code>{integer, ...}</code>
                  <span>Open tuple syntax. Maps use <code>%{foo: integer}</code>, <code>%{..., foo: integer}</code>, or <code>%{atom() =&gt; integer()}</code>.</span>
                </div>
                <div class="doc-note"><a href="https://elixir.hexdocs.pm/main/types-cheat.html" target="_blank" rel="noopener noreferrer">Types cheatsheet</a></div>
                <div class="doc-note">Use Ctrl+Enter, or Cmd+Enter on macOS, to run the input.</div>
              </div>
            </section>
          </div>
        </main>
      </div>

      <script>
        const examples = [
          ["Boolean tuple", "type pair = {boolean(), boolean} ;;\n{false, true} <= pair ;;"],
          ["Open tuple", "{integer, boolean} <= {integer, ...} ;;"],
          ["Function apply", "(integer() -> boolean -> integer()) integer boolean() ;;"],
          ["Multi-arity apply", "(integer, integer -> integer) (integer, integer) ;;"],
          ["Map access", "%{foo: integer, bar: boolean}[:foo] ;;\n%{atom() => integer()}[:foo] ;;"],
          ["Field select", "%{foo: integer, bar: boolean}.foo ;;\n%{foo: integer}.bar ;;"],
          ["Precision relation", "dynamic() <~ dynamic(integer()) ;;\ndynamic(integer()) <~ dynamic() ;;"],
          ["Consistent subtype", "dynamic(integer()) <=~ atom() ;;\ninteger() <=~ dynamic(atom()) ;;"],
          ["Compatibility", "integer() ~<= number() ;;\nnumber() ~<= integer() ;;"],
          ["Type variables", "{a, a} when a: term() ;;\n{a, a} when a: integer() ;;"],
          ["Tallying", "[ a <= integer() ] ;;\n[ a <= integer() ; integer() <= a ] ;;"],
          ["Precision", "precise? {x, y} when x == y ;;\nprecise? x when is_integer(x) ;;"],
          ["Lists", "list() ;;\nlist(integer, binary) ;;\nnon_empty_list(integer, binary) ;;"],
          ["Map clash", "%{foo: term()} and %{..., foo: term(), bar: term()} ;;"],
          ["Domain map", "%{atom() => integer()} ;;"],
          ["Operators", "integer or atom ;;\ninteger and not integer ;;\ninteger and not atom ;;\nnot integer and integer ;;"]
        ];

        const sessionKey = "elixir-types-repl-session";
        const session = localStorage.getItem(sessionKey) || newSession();
        localStorage.setItem(sessionKey, session);

        const input = document.querySelector("#input");
        const output = document.querySelector("#output");
        const aliases = document.querySelector("#aliases");
        const status = document.querySelector("#status");
        const dot = document.querySelector("#dot");

        function newSession() {
          if (window.crypto && crypto.randomUUID) {
            return crypto.randomUUID();
          }

          return String(Date.now()) + "-" + String(Math.random()).slice(2);
        }

        function setStatus(text, ok) {
          status.textContent = text;
          dot.classList.toggle("ok", Boolean(ok));
        }

        function clearEmpty() {
          const empty = output.querySelector(".empty");
          if (empty) empty.remove();
        }

        function addEntry(command, result, failed) {
          clearEmpty();

          const entry = document.createElement("div");
          entry.className = "entry";

          const cmd = document.createElement("pre");
          cmd.className = "cmd";
          cmd.textContent = command.trim();
          entry.appendChild(cmd);

          const body = document.createElement("pre");
          body.className = failed ? "error" : "result";
          body.textContent = result;
          entry.appendChild(body);

          output.prepend(entry);
        }

        function setAliases(names) {
          aliases.replaceChildren();

          if (!names.length) {
            const chip = document.createElement("span");
            chip.className = "chip";
            chip.textContent = "none";
            aliases.appendChild(chip);
            return;
          }

          for (const name of names) {
            const chip = document.createElement("span");
            chip.className = "chip";
            chip.textContent = name;
            aliases.appendChild(chip);
          }
        }

        async function post(path, payload) {
          const response = await fetch(path, {
            method: "POST",
            headers: {"content-type": "application/json"},
            body: JSON.stringify(payload)
          });

          return await response.json();
        }

        async function runInput() {
          const command = input.value.trim();
          if (!command) return;

          setStatus("Running", false);

          try {
            const result = await post("api/eval", {session, input: command});
            setAliases(result.aliases || []);

            if (result.ok) {
              addEntry(command, (result.output || []).join("\n") || "ok", false);
              setStatus("Ready", true);
            } else {
              addEntry(command, result.error || "error", true);
              setStatus("Error", false);
            }
          } catch (error) {
            addEntry(command, String(error), true);
            setStatus("Offline", false);
          }
        }

        async function resetSession() {
          const result = await post("api/reset", {session});
          setAliases(result.aliases || []);
          output.replaceChildren();
          const empty = document.createElement("div");
          empty.className = "empty";
          empty.textContent = "No results yet.";
          output.appendChild(empty);
          setStatus("Ready", result.ok);
        }

        for (const [label, code] of examples) {
          const button = document.createElement("button");
          button.type = "button";
          button.className = "example";
          button.textContent = label;
          button.addEventListener("click", () => {
            input.value = code;
            input.focus();
          });
          document.querySelector("#examples").appendChild(button);
        }

        document.querySelector("#run").addEventListener("click", runInput);
        input.addEventListener("keydown", (event) => {
          if ((event.ctrlKey || event.metaKey) && event.key === "Enter") {
            event.preventDefault();
            runInput();
          }
        });
        document.querySelector("#reset").addEventListener("click", resetSession);
        document.querySelector("#clearInput").addEventListener("click", () => {
          input.value = "";
          input.focus();
        });
        document.querySelector("#clearOutput").addEventListener("click", () => {
          output.replaceChildren();
          const empty = document.createElement("div");
          empty.className = "empty";
          empty.textContent = "No results yet.";
          output.appendChild(empty);
        });

        setStatus("Ready", true);
      </script>
    </body>
    </html>
    """
  end
end

defmodule Module.Types.Repl.Web.CLI do
  @moduledoc false

  alias Module.Types.Repl.Web

  def main(args) do
    {opts, rest, invalid} = OptionParser.parse(args, strict: [port: :integer])

    case {rest, invalid} do
      {[], []} ->
        Web.serve!(port: Keyword.get(opts, :port, 4100))

      _ ->
        IO.puts(:stderr, "usage: bin/elixir lib/elixir/scripts/types_repl_web.exs [--port PORT]")
        System.halt(1)
    end
  end
end
