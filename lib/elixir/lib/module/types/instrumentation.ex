# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

defmodule Module.Types.Instrumentation do
  @moduledoc false

  alias Module.Types.Descr

  @dir_env ~c"ELIXIR_GUARD_EXACTNESS_DIR"
  @project_env ~c"ELIXIR_GUARD_EXACTNESS_PROJECT"
  @repo_root_env ~c"ELIXIR_GUARD_EXACTNESS_REPO_ROOT"
  @run_id_env ~c"ELIXIR_GUARD_EXACTNESS_RUN_ID"
  @file_key {__MODULE__, :guard_exactness_file}

  @doc false
  def guard_exactness(kind, patterns, guards, expected, possible, exact?, tag, meta, stack) do
    case get_env(@dir_env) do
      nil ->
        :ok

      "" ->
        :ok

      dir ->
        row = [
          {"project", get_env(@project_env)},
          {"repo_root", get_env(@repo_root_env)},
          {"run_id", get_env(@run_id_env)},
          {"file", stack.file},
          {"module", term_to_string(stack.module)},
          {"function", format_function(stack.function)},
          {"line", source_line(meta, patterns)},
          {"column", source_column(meta, patterns)},
          {"site_kind", site_kind(kind, tag)},
          {"site_tag", format_tag(tag)},
          {"generated", keyword_get(meta, :generated, false) == true},
          {"stack_mode", atom_to_string(stack.mode)},
          {"reverse_arrow", format_reverse_arrow(stack.reverse_arrow)},
          {"patterns", map_list(patterns, &expr_to_string/1)},
          {"guards", map_list(guards, &expr_to_string/1)},
          {"guard_count", length(guards)},
          {"exact", exact? == true},
          {"possible_arg_types", map_list(possible, &type_to_string/1)},
          {"sure_arg_types", map_list(sure_types(possible, exact?), &type_to_string/1)},
          {"expected_arg_types", map_list(expected, &type_to_string/1)}
        ]

        write_jsonl!(dir, row)
    end
  end

  defp write_jsonl!(dir, row) do
    path =
      case :erlang.get(@file_key) do
        {^dir, path} ->
          path

        _ ->
          ensure_dir!(dir)

          path =
            join_path(
              dir,
              "guard-exactness-#{:erlang.system_time(:millisecond)}-#{:erlang.unique_integer([:positive])}-#{:erlang.phash2(self())}.jsonl"
            )

          :erlang.put(@file_key, {dir, path})
          path
      end

    write_file!(path, json_object(row) <> "\n")
  end

  defp get_env(name) do
    case :os.getenv(name) do
      false -> nil
      value -> :erlang.list_to_binary(value)
    end
  end

  defp ensure_dir!(dir) do
    case :filelib.ensure_dir(:erlang.binary_to_list(join_path(dir, ".keep"))) do
      :ok -> :ok
      {:error, reason} -> :erlang.error({:guard_exactness_mkdir_failed, dir, reason})
    end
  end

  defp write_file!(path, content) do
    case :file.write_file(:erlang.binary_to_list(path), content, [:append]) do
      :ok -> :ok
      {:error, reason} -> :erlang.error({:guard_exactness_write_failed, path, reason})
    end
  end

  defp join_path("", file), do: file

  defp join_path(dir, file) when :erlang.binary_part(dir, byte_size(dir), -1) == "/",
    do: dir <> file

  defp join_path(dir, file), do: dir <> "/" <> file

  defp sure_types(possible, true), do: possible
  defp sure_types(possible, false), do: duplicate(Descr.none(), length(possible))

  defp source_line(meta, patterns), do: keyword_get(meta, :line, nil) || ast_meta(patterns, :line)
  defp source_column(meta, patterns), do: keyword_get(meta, :column, nil) || ast_meta(patterns, :column)

  defp ast_meta(patterns, key) do
    find_value(patterns, fn
      {_, meta, _} when is_list(meta) -> keyword_get(meta, key, nil)
      _ -> nil
    end)
  end

  defp format_function({fun, arity}) when is_atom(fun) and is_integer(arity) do
    atom_to_string(fun) <> "/" <> :erlang.integer_to_binary(arity)
  end

  defp format_function(other), do: term_to_string(other)

  defp format_reverse_arrow(nil), do: nil
  defp format_reverse_arrow(atom) when is_atom(atom), do: atom_to_string(atom)
  defp format_reverse_arrow(other), do: term_to_string(other)

  defp format_tag(tag), do: term_to_string(tag)

  defp site_kind(kind, _tag) when kind in [:for, :with], do: atom_to_string(kind)
  defp site_kind(:head, {{:case, _meta, _expr, _type}, _head}), do: "case"
  defp site_kind(:head, {{{:case, _meta, _expr, _type}, _head}, _}), do: "case"
  defp site_kind(:head, {{:with_else, _else_types}, _head}), do: "with_else"
  defp site_kind(:head, {:fn, _head}), do: "fn"
  defp site_kind(:head, {:try_catch, _head}), do: "try_catch"
  defp site_kind(:head, {:receive, _head}), do: "receive"
  defp site_kind(:head, {:for_reduce, _head}), do: "for_reduce"
  defp site_kind(:head, {{{:def, kind, _fun, _expected}, _args, _guards}, _head}),
    do: atom_to_string(kind)

  defp site_kind(:head, {{:def, kind, _fun, _expected}, _args, _guards}), do: atom_to_string(kind)
  defp site_kind(kind, _tag), do: atom_to_string(kind)

  defp expr_to_string(expr), do: term_to_string(expr)
  defp type_to_string(type), do: term_to_string(type)

  defp atom_to_string(atom), do: :erlang.atom_to_binary(atom, :utf8)

  defp term_to_string(term) do
    case :unicode.characters_to_binary(:io_lib.format(~c"~tp", [term])) do
      binary when is_binary(binary) -> binary
      _ -> "<<unprintable>>"
    end
  catch
    _, _ -> "<<unprintable>>"
  end

  defp json_object(entries) do
    "{" <> join(map_list(entries, fn {key, value} -> json_encode(key) <> ":" <> json_encode(value) end), ",") <> "}"
  end

  defp json_encode(value) when is_list(value) do
    "[" <> join(map_list(value, &json_encode/1), ",") <> "]"
  end

  defp json_encode(value) when is_binary(value), do: "\"" <> json_escape(value) <> "\""
  defp json_encode(value) when is_integer(value), do: :erlang.integer_to_binary(value)
  defp json_encode(value) when is_float(value), do: :erlang.float_to_binary(value, [:short])
  defp json_encode(true), do: "true"
  defp json_encode(false), do: "false"
  defp json_encode(nil), do: "null"

  defp json_escape(value), do: json_escape(value, [])

  defp json_escape(<<>>, acc), do: :erlang.iolist_to_binary(:lists.reverse(acc))
  defp json_escape(<<?\\, rest::binary>>, acc), do: json_escape(rest, ["\\\\" | acc])
  defp json_escape(<<?", rest::binary>>, acc), do: json_escape(rest, ["\\\"" | acc])
  defp json_escape(<<?\b, rest::binary>>, acc), do: json_escape(rest, ["\\b" | acc])
  defp json_escape(<<?\f, rest::binary>>, acc), do: json_escape(rest, ["\\f" | acc])
  defp json_escape(<<?\n, rest::binary>>, acc), do: json_escape(rest, ["\\n" | acc])
  defp json_escape(<<?\r, rest::binary>>, acc), do: json_escape(rest, ["\\r" | acc])
  defp json_escape(<<?\t, rest::binary>>, acc), do: json_escape(rest, ["\\t" | acc])

  defp json_escape(<<codepoint::utf8, rest::binary>>, acc) when codepoint < 0x20 do
    json_escape(rest, [unicode_escape(codepoint) | acc])
  end

  defp json_escape(<<codepoint::utf8, rest::binary>>, acc) do
    json_escape(rest, [<<codepoint::utf8>> | acc])
  end

  defp unicode_escape(codepoint) do
    "\\u" <> pad_leading(:erlang.integer_to_binary(codepoint, 16), 4, "0")
  end

  defp pad_leading(value, size, _pad) when byte_size(value) >= size, do: value
  defp pad_leading(value, size, pad), do: pad_leading(pad <> value, size, pad)

  defp map_list([], _fun), do: []
  defp map_list([head | tail], fun), do: [fun.(head) | map_list(tail, fun)]

  defp duplicate(_value, 0), do: []
  defp duplicate(value, count), do: [value | duplicate(value, count - 1)]

  defp find_value([], _fun), do: nil

  defp find_value([head | tail], fun) do
    case fun.(head) do
      nil -> find_value(tail, fun)
      value -> value
    end
  end

  defp keyword_get([], _key, default), do: default
  defp keyword_get([{key, value} | _tail], key, _default), do: value
  defp keyword_get([_head | tail], key, default), do: keyword_get(tail, key, default)

  defp join([], _separator), do: ""
  defp join([head | tail], separator), do: join(tail, separator, head)
  defp join([], _separator, acc), do: acc
  defp join([head | tail], separator, acc), do: join(tail, separator, acc <> separator <> head)
end
