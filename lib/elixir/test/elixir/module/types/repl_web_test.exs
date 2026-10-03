# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

Code.require_file("type_helper.exs", __DIR__)

defmodule Module.Types.ReplWebTest do
  use ExUnit.Case, async: true

  alias Module.Types.Repl.Web

  setup do
    {:ok, server} = Web.start_link(port: 0)

    on_exit(fn ->
      Web.stop(server)
    end)

    %{server: server}
  end

  test "serves the web UI", %{server: server} do
    {200, _headers, body} = request(server, "GET", "/")

    assert body =~ "<title>Elixir Types REPL</title>"
    assert body =~ ~s(id="input")
    assert body =~ "api/eval"
    assert body =~ "{integer, ...}"
    assert body =~ "%{..., foo: term(), bar: term()}"
    assert body =~ "t[s]"
    assert body =~ "t.a"
    assert body =~ "a &lt;~ b"
    assert body =~ "a &lt;=~ b"
    assert body =~ "a ~&lt;= b"
    assert body =~ "t when a: bound"
    assert body =~ "[a &lt;= b ; ...]"
    assert body =~ "precise? head"
    assert body =~ "types-cheat.html"
    assert body =~ "Ctrl+Enter"
  end

  test "evaluates commands and preserves aliases by session", %{server: server} do
    session = "repl-web-test"

    {200, _headers, body} =
      request(
        server,
        "POST",
        "/api/eval",
        JSON.encode!(%{
          session: session,
          input: "type pair = {boolean(), boolean} ;; {false, true} <= pair ;;"
        })
      )

    assert %{"ok" => true, "output" => ["true"], "aliases" => ["pair"]} = JSON.decode!(body)

    {200, _headers, body} =
      request(
        server,
        "POST",
        "/api/eval",
        JSON.encode!(%{session: session, input: "{false, true} <= pair ;;"})
      )

    assert %{"ok" => true, "output" => ["true"], "aliases" => ["pair"]} = JSON.decode!(body)
  end

  test "evaluates map projections", %{server: server} do
    session = "repl-web-projection-test"

    {200, _headers, body} =
      request(
        server,
        "POST",
        "/api/eval",
        JSON.encode!(%{session: session, input: "%{foo: integer}[:foo] ;;"})
      )

    assert %{"ok" => true, "output" => ["integer()"], "aliases" => []} = JSON.decode!(body)

    {200, _headers, body} =
      request(
        server,
        "POST",
        "/api/eval",
        JSON.encode!(%{session: session, input: "%{foo: integer}.foo ;;"})
      )

    assert %{"ok" => true, "output" => ["integer()"], "aliases" => []} = JSON.decode!(body)
  end

  test "evaluates precision checks", %{server: server} do
    session = "repl-web-precision-test"

    {200, _headers, body} =
      request(
        server,
        "POST",
        "/api/eval",
        JSON.encode!(%{session: session, input: "precise? {x, y} when x == y ;;"})
      )

    assert %{"ok" => true, "output" => ["false"], "aliases" => []} = JSON.decode!(body)
  end

  test "evaluates type variables", %{server: server} do
    session = "repl-web-type-variables-test"

    {200, _headers, body} =
      request(
        server,
        "POST",
        "/api/eval",
        JSON.encode!(%{session: session, input: "{a, a} when a: integer() ;;"})
      )

    assert %{"ok" => true, "output" => ["{a and integer(), a and integer()}"], "aliases" => []} =
             JSON.decode!(body)
  end

  test "evaluates tallying constraints", %{server: server} do
    session = "repl-web-tally-test"

    {200, _headers, body} =
      request(
        server,
        "POST",
        "/api/eval",
        JSON.encode!(%{session: session, input: "[ a <= integer() ; integer() <= a ] ;;"})
      )

    assert %{"ok" => true, "output" => ["[\n  a: integer()\n]"], "aliases" => []} =
             JSON.decode!(body)
  end

  test "resets a session", %{server: server} do
    session = "repl-web-reset-test"

    {200, _headers, _body} =
      request(
        server,
        "POST",
        "/api/eval",
        JSON.encode!(%{session: session, input: "type pair = {boolean(), boolean} ;;"})
      )

    {200, _headers, body} =
      request(server, "POST", "/api/reset", JSON.encode!(%{session: session}))

    assert %{"ok" => true, "aliases" => []} = JSON.decode!(body)

    {200, _headers, body} =
      request(
        server,
        "POST",
        "/api/eval",
        JSON.encode!(%{session: session, input: "{false, true} <= pair ;;"})
      )

    assert %{"ok" => true, "aliases" => [], "output" => ["false"]} = JSON.decode!(body)
  end

  defp request(server, method, path, body \\ "") do
    {:ok, socket} = :gen_tcp.connect({127, 0, 0, 1}, server.port, [:binary, active: false])

    :ok =
      :gen_tcp.send(socket, [
        method,
        " ",
        path,
        " HTTP/1.1\r\n",
        "Host: 127.0.0.1\r\n",
        "Content-Type: application/json\r\n",
        "Content-Length: ",
        Integer.to_string(byte_size(body)),
        "\r\n",
        "Connection: close\r\n",
        "\r\n",
        body
      ])

    response = recv_all(socket, "")
    :gen_tcp.close(socket)

    [head, body] = String.split(response, "\r\n\r\n", parts: 2)
    [status_line | header_lines] = String.split(head, "\r\n")
    ["HTTP/1.1", status | _] = String.split(status_line, " ")

    headers =
      Map.new(header_lines, fn line ->
        [key, value] = String.split(line, ":", parts: 2)
        {String.downcase(key), String.trim(value)}
      end)

    {String.to_integer(status), headers, body}
  end

  defp recv_all(socket, acc) do
    case :gen_tcp.recv(socket, 0, 1_000) do
      {:ok, data} -> recv_all(socket, acc <> data)
      {:error, :closed} -> acc
    end
  end
end
