# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

defmodule Module.Types.Repl do
  @moduledoc false

  alias Module.Types
  alias Module.Types.Descr
  alias Module.Types.Pattern

  defstruct aliases: %{}, variables: %{}

  @help """
  Elixir set-theoretic types REPL

  Commands end with `;;`.

      type pair = {boolean(), boolean} ;;
      {false, true} <= pair ;;
      {integer, boolean} <= {integer, ...} ;;
      %{foo: term()} and %{..., foo: term(), bar: term()} ;;
      (binary(), binary() -> binary()) ;;
      ((integer, integer) -> integer) (integer, integer) ;;
      %{foo: integer, bar: boolean}[:foo] ;;
      %{foo: integer, bar: boolean}.foo ;;
      dynamic() <~ dynamic(integer()) ;;
      dynamic(integer()) <=~ atom() ;;
      integer() ~<= number() ;;
      {a, a} when a: integer() ;;
      [ a <= integer() ; integer() <= a ] ;;
      precise? {x, y} when x == y ;;
      (integer() -> boolean -> integer()) integer boolean() ;;

  Supported constructors:

      none, term, dynamic, atom, boolean, integer, float, number
      binary, bitstring, pid, port, reference
      tuple, map, record, arrow, fun, function, list, empty_list
      empty_map, non_empty_list, if_set, not_set

  Zero-arity constructors can be written with or without parentheses:

      integer, boolean, term, dynamic
      integer(), boolean(), term(), dynamic()

  Supported operators:

      not t          negation
      t and not s    difference
      t and s        intersection
      t or s         union
      t -> s         function type
      t s            function application
      t (s1, s2)     multi-arity function application
      t[s]           Elixir map access
      t.a            required map/record field selection
      [t <= s ; ...] tally subtype constraints
      precise? head   pattern/guard precision test
      t <= s         subtyping test
      t <=~ s        consistent subtyping test
      t <~ s         precision test, also written t <~= s
      t ~<= s        compatibility test
      t = s          semantic equality test
      t >= s         reverse subtyping test

  Bare identifiers that are not aliases or constructors are atom singletons.
  Capitalized identifiers are Elixir aliases, as in `URI` or `Foo.Bar`.
  Tuple types use braces. Open tuple tails use `...`, as in `{integer, ...}`.
  List aliases are `list()`, `list(t)`, and `list(t, tail)`.
  Map types use `%{key: type}` for closed maps and `%{..., key: type}` for open maps.
  Domain maps such as `%{atom() => integer()}` are also supported.
  Field selection such as `t.a` errors if `:a` is not guaranteed to be present.
  Type variables are local to a type expression:

      {a, a} when a: term()
      {a, a} when a: integer()
  """

  def new, do: %__MODULE__{}

  def help, do: @help

  def split_commands(input) when is_binary(input) do
    parts = String.split(input, ";;")
    {commands, [rest]} = Enum.split(parts, -1)

    commands =
      commands
      |> Enum.map(&String.trim/1)
      |> Enum.reject(&(&1 == ""))

    {commands, rest}
  end

  def eval(input, state \\ new()) when is_binary(input) do
    {commands, rest} = split_commands(input)

    commands =
      case String.trim(rest) do
        "" -> commands
        rest -> commands ++ [rest]
      end

    Enum.reduce_while(commands, {:ok, [], state}, fn command, {:ok, output, state} ->
      case eval_command(command, state) do
        {:ok, nil, state} -> {:cont, {:ok, output, state}}
        {:ok, result, state} -> {:cont, {:ok, output ++ [result], state}}
        {:error, message, state} -> {:halt, {:error, message, state}}
      end
    end)
  end

  def eval_command(command, state \\ new()) when is_binary(command) do
    try do
      {result, state} = parse_command(command, state)

      {:ok, format_result(result), state}
    catch
      {:repl_error, message} ->
        {:error, message, state}
    end
  end

  defp format_result({:type, type}), do: Descr.to_quoted_string(type)
  defp format_result({:boolean, boolean}), do: Atom.to_string(boolean)
  defp format_result({:tally, solutions}), do: format_tally_solutions(solutions)
  defp format_result({:text, text}), do: text
  defp format_result(:ok), do: nil

  defp parse_command(command, state) when is_binary(command) do
    command = String.trim(command)

    if String.starts_with?(command, "precise?") do
      parse_precise_command(command, state)
    else
      command
      |> tokenize()
      |> parse_command(state)
    end
  end

  defp parse_command([{:id, "help"} | rest], state) do
    expect_end!(rest)
    {{:text, @help}, state}
  end

  defp parse_command([{:id, "type"}, {:id, name}, :eq | rest], state) do
    {type, rest} = parse_type(rest, state)
    expect_end!(rest)

    {:ok, type} = as_type(type)

    {:ok, %{state | aliases: Map.put(state.aliases, name, type)}}
  end

  defp parse_command([:lbracket | rest], state) do
    tally_state = tally_state(rest, state)
    {constraints, rest} = parse_tally_constraints(rest, tally_state, [])
    expect_end!(rest)

    solutions =
      try do
        Descr.tally(constraints)
      rescue
        exception in ArgumentError ->
          error!("tallying failed: #{Exception.message(exception)}")
      end

    {{:tally, solutions}, state}
  end

  defp parse_command(tokens, state) do
    {left, rest} = parse_type(tokens, state)

    case rest do
      [:lte | rest] ->
        {right, rest} = parse_type(rest, state)
        expect_end!(rest)
        {{:boolean, subtype?(left, right)}, state}

      [:gte | rest] ->
        {right, rest} = parse_type(rest, state)
        expect_end!(rest)
        {{:boolean, subtype?(right, left)}, state}

      [:consistent_subtype | rest] ->
        {right, rest} = parse_type(rest, state)
        expect_end!(rest)
        {{:boolean, consistent_subtype?(left, right)}, state}

      [:precision | rest] ->
        {right, rest} = parse_type(rest, state)
        expect_end!(rest)
        {{:boolean, precision?(left, right)}, state}

      [:compatible | rest] ->
        {right, rest} = parse_type(rest, state)
        expect_end!(rest)
        {{:boolean, compatible?(left, right)}, state}

      [:eq | rest] ->
        {right, rest} = parse_type(rest, state)
        expect_end!(rest)
        {{:boolean, equal?(left, right)}, state}

      [:eof] ->
        {:ok, type} = as_type(left)
        {{:type, type}, state}

      [token | _] ->
        error!("unexpected token #{format_token(token)}")
    end
  end

  defp subtype?(left, right) do
    {:ok, left} = as_type(left)
    {:ok, right} = as_type(right)
    Descr.subtype?(left, right)
  end

  defp precision?(left, right) do
    {:ok, left} = as_type(left)
    {:ok, right} = as_type(right)

    Descr.subtype?(Descr.lower_bound(left), Descr.lower_bound(right)) and
      Descr.subtype?(Descr.upper_bound(right), Descr.upper_bound(left))
  end

  defp consistent_subtype?(left, right) do
    {:ok, left} = as_type(left)
    {:ok, right} = as_type(right)

    Descr.subtype?(Descr.lower_bound(left), Descr.upper_bound(right))
  end

  defp compatible?(left, right) do
    {:ok, left} = as_type(left)
    {:ok, right} = as_type(right)

    Descr.compatible?(left, right)
  end

  defp equal?(left, right) do
    {:ok, left} = as_type(left)
    {:ok, right} = as_type(right)
    Descr.equal?(left, right)
  end

  defp parse_tally_constraints([:rbracket | rest], _state, acc), do: {Enum.reverse(acc), rest}

  defp parse_tally_constraints(tokens, state, acc) do
    {left, rest} = parse_type(tokens, state)

    case rest do
      [:lte | rest] ->
        {right, rest} = parse_type(rest, state)
        {:ok, left} = as_type(left)
        {:ok, right} = as_type(right)
        parse_tally_separator([{left, right} | acc], rest, state)

      [token | _] ->
        error!("expected `<=` in tallying constraint, got #{format_token(token)}")
    end
  end

  defp parse_tally_separator(acc, [:semicolon | rest], state),
    do: parse_tally_constraints(rest, state, acc)

  defp parse_tally_separator(acc, [:comma | rest], state),
    do: parse_tally_constraints(rest, state, acc)

  defp parse_tally_separator(acc, [:rbracket | rest], _state), do: {Enum.reverse(acc), rest}

  defp parse_tally_separator(_acc, [token | _], _state) do
    error!("expected `;` or `]` after tallying constraint, got #{format_token(token)}")
  end

  defp tally_state(tokens, state) do
    variables =
      tokens
      |> Enum.flat_map(fn
        {:id, id} ->
          if tally_variable_identifier?(id, state), do: [id], else: []

        _ ->
          []
      end)
      |> Enum.uniq()
      |> Map.new(fn id -> {id, Descr.var(String.to_atom(id))} end)

    %{state | variables: variables}
  end

  defp tally_variable_identifier?(id, state) do
    not Map.has_key?(state.aliases, id) and builtin_type(id) == nil and not alias_identifier?(id)
  end

  defp parse_type(tokens, state) do
    case split_type_variable_constraints(tokens) do
      {:ok, type_tokens, constraint_tokens} ->
        {state, rest} = parse_type_variable_constraints(constraint_tokens, state)
        {type, [:eof]} = parse_arrow(type_tokens ++ [:eof], state)
        {type, rest}

      :error ->
        parse_arrow(tokens, state)
    end
  end

  defp split_type_variable_constraints(tokens) do
    split_type_variable_constraints(tokens, 0, [])
  end

  defp split_type_variable_constraints([:when | rest], 0, acc) do
    {:ok, Enum.reverse(acc), rest}
  end

  defp split_type_variable_constraints([token | _rest], 0, _acc)
       when token in [
              :comma,
              :rparen,
              :rbrace,
              :rbracket,
              :lte,
              :gte,
              :consistent_subtype,
              :precision,
              :compatible,
              :eq,
              :eof
            ] do
    :error
  end

  defp split_type_variable_constraints([token | rest], depth, acc)
       when token in [:lparen, :lbrace, :lbracket, :percent_lbrace] do
    split_type_variable_constraints(rest, depth + 1, [token | acc])
  end

  defp split_type_variable_constraints([token | rest], depth, acc)
       when token in [:rparen, :rbrace, :rbracket] and depth > 0 do
    split_type_variable_constraints(rest, depth - 1, [token | acc])
  end

  defp split_type_variable_constraints([token | rest], depth, acc) do
    split_type_variable_constraints(rest, depth, [token | acc])
  end

  defp split_type_variable_constraints([], _depth, _acc), do: :error

  defp parse_type_variable_constraints(tokens, state) do
    {constraints, rest} = parse_type_variable_constraints(tokens, state, [])

    variables =
      Map.new(constraints, fn {name, bound} ->
        variable = Descr.var(String.to_atom(name))
        replacement = restrict_type_variable(variable, bound)
        {name, replacement}
      end)

    {%{state | variables: variables}, rest}
  end

  defp parse_type_variable_constraints([{:id, name}, :colon | rest], state, acc) do
    {bound, rest} = parse_type(rest, %{state | variables: %{}})
    {:ok, bound} = as_type(bound)
    acc = [{name, bound} | acc]

    case rest do
      [:comma | rest] -> parse_type_variable_constraints(rest, state, acc)
      _ -> {Enum.reverse(acc), rest}
    end
  end

  defp parse_type_variable_constraints([token | _rest], _state, _acc) do
    error!("expected type variable constraint, got #{format_token(token)}")
  end

  defp restrict_type_variable(variable, bound) do
    if Descr.equal?(bound, Descr.term()) do
      variable
    else
      Descr.opt_intersection(variable, bound)
    end
  end

  defp parse_arrow(tokens, state) do
    {left, rest} = parse_union(tokens, state)

    case rest do
      [:arrow | rest] ->
        {right, rest} = parse_arrow(rest, state)
        {:ok, right} = as_type(right)
        {function_type(left, right), rest}

      _ ->
        {left, rest}
    end
  end

  defp parse_union(tokens, state) do
    {left, rest} = parse_intersection(tokens, state)
    parse_union(left, rest, state)
  end

  defp parse_union(left, [operator | rest], state) when operator in [:or, :bar] do
    {right, rest} = parse_intersection(rest, state)
    {:ok, left} = as_type(left)
    {:ok, right} = as_type(right)
    parse_union(type(Descr.opt_union(left, right)), rest, state)
  end

  defp parse_union(left, rest, _state), do: {left, rest}

  defp parse_intersection(tokens, state) do
    {left, rest} = parse_difference(tokens, state)
    parse_intersection(left, rest, state)
  end

  defp parse_intersection(left, [:and, :not | rest], state) do
    {right, rest} = parse_unary(rest, state)
    {:ok, left} = as_type(left)
    {:ok, right} = as_type(right)
    parse_intersection(type(Descr.opt_difference(left, right)), rest, state)
  end

  defp parse_intersection(left, [operator | rest], state) when operator in [:and, :amp] do
    {right, rest} = parse_difference(rest, state)
    {:ok, left} = as_type(left)
    {:ok, right} = as_type(right)
    parse_intersection(type(Descr.opt_intersection(left, right)), rest, state)
  end

  defp parse_intersection(left, rest, _state), do: {left, rest}

  defp parse_difference(tokens, state) do
    {left, rest} = parse_unary(tokens, state)
    parse_difference(left, rest, state)
  end

  defp parse_difference(left, [:backslash | rest], state) do
    {right, rest} = parse_unary(rest, state)
    {:ok, left} = as_type(left)
    {:ok, right} = as_type(right)
    parse_difference(type(Descr.opt_difference(left, right)), rest, state)
  end

  defp parse_difference(left, rest, _state), do: {left, rest}

  defp parse_unary([operator | rest], state) when operator in [:not, :tilde] do
    {inner, rest} = parse_unary(rest, state)
    {:ok, inner} = as_type(inner)
    {type(Descr.opt_negation(inner)), rest}
  end

  defp parse_unary(tokens, state), do: parse_application(tokens, state)

  defp parse_application(tokens, state) do
    {left, rest} = parse_postfix(tokens, state)
    parse_application(left, rest, state)
  end

  defp parse_application(left, [token | _] = tokens, state)
       when token in [:not, :tilde, :lparen, :lbrace, :percent_lbrace] do
    {arg, rest} = parse_application_arg(tokens, state)
    parse_application(apply_type(left, arg), rest, state)
  end

  defp parse_application(left, [{kind, _} | _] = tokens, state)
       when kind in [:id, :atom, :integer] do
    {arg, rest} = parse_application_arg(tokens, state)
    parse_application(apply_type(left, arg), rest, state)
  end

  defp parse_application(left, rest, _state), do: {left, rest}

  defp parse_application_arg([operator | rest], state) when operator in [:not, :tilde] do
    {inner, rest} = parse_application_arg(rest, state)
    {:ok, inner} = as_type(inner)
    {type(Descr.opt_negation(inner)), rest}
  end

  defp parse_application_arg(tokens, state), do: parse_postfix(tokens, state)

  defp parse_postfix(tokens, state) do
    {expr, rest} = parse_primary(tokens, state)
    parse_postfix_rest(expr, rest, state)
  end

  defp parse_postfix_rest(expr, [:lbracket | rest], state) do
    {key, rest} = parse_type(rest, state)

    case rest do
      [:rbracket | rest] ->
        parse_postfix_rest(project_map(expr, key), rest, state)

      [token | _] ->
        error!("expected `]`, got #{format_token(token)}")
    end
  end

  defp parse_postfix_rest(expr, [:dot, {:id, field} | rest], state) do
    parse_postfix_rest(select_field(expr, field), rest, state)
  end

  defp parse_postfix_rest(_expr, [:dot, token | _rest], _state) do
    error!("expected field name after `.`, got #{format_token(token)}")
  end

  defp parse_postfix_rest(expr, [:question | rest], state) do
    {:ok, type} = as_type(expr)
    parse_postfix_rest(type(Descr.if_set(type)), rest, state)
  end

  defp parse_postfix_rest(expr, rest, _state), do: {expr, rest}

  defp parse_primary([:lparen, :rparen | rest], _state), do: {domain([]), rest}

  defp parse_primary([:lparen, :arrow | rest], state) do
    {return, rest} = parse_type(rest, state)

    case rest do
      [:rparen | rest] ->
        {:ok, return} = as_type(return)
        {type(Descr.fun([], return)), rest}

      [token | _] ->
        error!("expected `)`, got #{format_token(token)}")
    end
  end

  defp parse_primary([:lparen | rest], state) do
    {first, rest} = parse_type(rest, state)

    case rest do
      [:comma | rest] ->
        parse_domain([first], rest, state)

      [:rparen | rest] ->
        {first, rest}

      [token | _] ->
        error!("expected `)` or `,`, got #{format_token(token)}")
    end
  end

  defp parse_primary([:lbrace, :rbrace | rest], _state), do: {tuple([]), rest}
  defp parse_primary([:lbrace, :ellipsis, :rbrace | rest], _state), do: {tuple([], :open), rest}
  defp parse_primary([:lbrace | rest], state), do: parse_tuple(rest, state)
  defp parse_primary([:percent_lbrace | rest], state), do: parse_map(rest, state)

  defp parse_primary([{:id, id}, :lparen | rest], state) do
    {args, rest} = parse_call_args(rest, state)
    {constructor_call(id, args, state), rest}
  end

  defp parse_primary([{:id, id} | rest], state) do
    {resolve_identifier(id, state), rest}
  end

  defp parse_primary([{:atom, atom} | rest], _state), do: {type(Descr.atom([atom])), rest}
  defp parse_primary([{:integer, _integer} | rest], _state), do: {type(Descr.integer()), rest}
  defp parse_primary([:eof], _state), do: error!("expected type, got end of input")
  defp parse_primary([token | _], _state), do: error!("expected type, got #{format_token(token)}")

  defp parse_domain(acc, [:rparen | rest], _state) do
    acc
    |> Enum.reverse()
    |> domain()
    |> then(&{&1, rest})
  end

  defp parse_domain(acc, tokens, state) do
    {expr, rest} = parse_union(tokens, state)

    case rest do
      [:comma | rest] -> parse_domain([expr | acc], rest, state)
      [:arrow | rest] -> parse_parenthesized_fun([expr | acc], rest, state)
      [:rparen | rest] -> parse_domain([expr | acc], [:rparen | rest], state)
      [token | _] -> error!("expected `,`, `->`, or `)`, got #{format_token(token)}")
    end
  end

  defp parse_parenthesized_fun(args, tokens, state) do
    {return, rest} = parse_type(tokens, state)

    case rest do
      [:rparen | rest] ->
        args =
          args
          |> Enum.reverse()
          |> Enum.map(fn arg -> elem(as_type(arg), 1) end)

        {:ok, return} = as_type(return)
        {type(Descr.fun(args, return)), rest}

      [token | _] ->
        error!("expected `)`, got #{format_token(token)}")
    end
  end

  defp parse_tuple(tokens, state) do
    {first, rest} = parse_type(tokens, state)
    parse_tuple([first], rest, state)
  end

  defp parse_tuple(acc, [:comma, :ellipsis, :rbrace | rest], _state) do
    acc
    |> Enum.reverse()
    |> tuple(:open)
    |> then(&{&1, rest})
  end

  defp parse_tuple(acc, [:rbrace | rest], _state) do
    acc
    |> Enum.reverse()
    |> tuple()
    |> then(&{&1, rest})
  end

  defp parse_tuple(acc, [:comma | rest], state) do
    {expr, rest} = parse_type(rest, state)
    parse_tuple([expr | acc], rest, state)
  end

  defp parse_tuple(_acc, [token | _], _state) do
    error!("expected `,`, `...`, or `}`, got #{format_token(token)}")
  end

  defp parse_call_args([:rparen | rest], _state), do: {[], rest}

  defp parse_call_args(tokens, state) do
    {arg, rest} = parse_type(tokens, state)
    parse_call_args([arg], rest, state)
  end

  defp parse_call_args(acc, [:comma | rest], state) do
    {arg, rest} = parse_type(rest, state)
    parse_call_args([arg | acc], rest, state)
  end

  defp parse_call_args(acc, [:rparen | rest], _state), do: {Enum.reverse(acc), rest}

  defp parse_call_args(_acc, [token | _], _state),
    do: error!("expected `,` or `)`, got #{format_token(token)}")

  defp parse_map([:rbrace | rest], _state), do: {type(Descr.empty_map()), rest}

  defp parse_map(tokens, state), do: parse_map_fields([], :closed, tokens, state)

  defp parse_map_fields(fields, tag, [:rbrace | rest], _state) do
    {map_type(Enum.reverse(fields), tag), rest}
  end

  defp parse_map_fields(fields, _tag, [tail, :rbrace | rest], _state)
       when tail in [:ellipsis, :dotdot] do
    {map_type(Enum.reverse(fields), :open), rest}
  end

  defp parse_map_fields(fields, _tag, [tail, :comma | rest], state)
       when tail in [:ellipsis, :dotdot] do
    parse_map_fields(fields, :open, rest, state)
  end

  defp parse_map_fields(fields, tag, tokens, state) do
    {field, rest} = parse_map_field(tokens, state)
    parse_map_field_separator([field | fields], tag, rest, state)
  end

  defp parse_map_field_separator(fields, tag, [:semicolon | rest], state) do
    parse_map_fields(fields, tag, rest, state)
  end

  defp parse_map_field_separator(fields, tag, [:comma | rest], state) do
    parse_map_fields(fields, tag, rest, state)
  end

  defp parse_map_field_separator(fields, tag, [:rbrace | _] = rest, state) do
    parse_map_fields(fields, tag, rest, state)
  end

  defp parse_map_field_separator(fields, tag, [tail | _] = rest, state)
       when tail in [:ellipsis, :dotdot] do
    parse_map_fields(fields, tag, rest, state)
  end

  defp parse_map_field_separator(_fields, _tag, [token | _], _state) do
    error!("expected `;`, `,`, `...`, or `}`, got #{format_token(token)}")
  end

  defp parse_map_field([{:id, id}, :colon | rest], state) do
    {value, rest} = parse_type(rest, state)
    {:ok, value} = as_type(value)
    {{String.to_atom(id), value}, rest}
  end

  defp parse_map_field([{:atom, atom}, :colon | rest], state) do
    {value, rest} = parse_type(rest, state)
    {:ok, value} = as_type(value)
    {{atom, value}, rest}
  end

  defp parse_map_field(tokens, state) do
    {key, rest} = parse_type(tokens, state)

    case rest do
      [:fat_arrow | rest] ->
        {:ok, key} = as_type(key)
        {value, rest} = parse_type(rest, state)
        {:ok, value} = as_type(value)
        {{Descr.to_domain_keys(key), value}, rest}

      [token | _] ->
        error!("expected `:` or `=>`, got #{format_token(token)}")
    end
  end

  defp map_type(fields, :closed), do: type(Descr.closed_map(fields))
  defp map_type(fields, :open), do: type(Descr.open_map(fields))

  defp constructor_call(id, args, state) do
    types = Enum.map(args, fn arg -> elem(as_type(arg), 1) end)

    case {id, args, types} do
      {"atom", [], []} ->
        type(Descr.atom())

      {"bool", [], []} ->
        type(Descr.boolean())

      {"boolean", [], []} ->
        type(Descr.boolean())

      {"dynamic", [], []} ->
        type(Descr.dynamic())

      {"dynamic", [_], [arg]} ->
        type(Descr.dynamic(arg))

      {"fun", [], []} ->
        type(Descr.fun())

      {"function", [], []} ->
        type(Descr.fun())

      {"arrow", [], []} ->
        type(Descr.fun())

      {"tuple", [], []} ->
        type(Descr.tuple())

      {"tuple", [_ | _], types} ->
        tuple_from_types(types)

      {"open_tuple", [_ | _], types} ->
        type(Descr.open_tuple(types))

      {"map", [], []} ->
        type(Descr.open_map())

      {"record", [], []} ->
        type(Descr.open_map())

      {"empty_map", [], []} ->
        type(Descr.empty_map())

      {"empty_list", [], []} ->
        type(Descr.empty_list())

      {"list", [], []} ->
        type(Descr.list(Descr.term()))

      {"list", [arg], [_]} ->
        type(Descr.list(elem(as_type(arg), 1)))

      {"list", [arg, tail], [_, _]} ->
        type(
          Descr.opt_union(
            Descr.empty_list(),
            Descr.non_empty_list(elem(as_type(arg), 1), elem(as_type(tail), 1))
          )
        )

      {"non_empty_list", [arg], [_]} ->
        type(Descr.non_empty_list(elem(as_type(arg), 1)))

      {"non_empty_list", [arg, tail], [_, _]} ->
        type(Descr.non_empty_list(elem(as_type(arg), 1), elem(as_type(tail), 1)))

      {"if_set", [arg], [_]} ->
        type(Descr.if_set(elem(as_type(arg), 1)))

      {"not_set", [], []} ->
        type(Descr.not_set())

      {"fun", [domain, _return], [_, return_type]} ->
        type(Descr.fun(function_args(domain), return_type))

      {"arrow", [domain, _return], [_, return_type]} ->
        type(Descr.fun(function_args(domain), return_type))

      {known, [], []} ->
        resolve_identifier(known, state)

      {unknown, _, _} ->
        error!("unknown type constructor #{unknown}/#{length(args)}")
    end
  end

  defp resolve_identifier(id, state) do
    cond do
      Map.has_key?(state.aliases, id) -> type(Map.fetch!(state.aliases, id))
      builtin = builtin_type(id) -> type(builtin)
      variable = Map.get(state.variables, id) -> type(variable)
      true -> type(Descr.atom([identifier_atom(id)]))
    end
  end

  defp builtin_type("empty"), do: Descr.none()
  defp builtin_type("none"), do: Descr.none()
  defp builtin_type("any"), do: Descr.term()
  defp builtin_type("term"), do: Descr.term()
  defp builtin_type("dynamic"), do: Descr.dynamic()
  defp builtin_type("atom"), do: Descr.atom()
  defp builtin_type("bool"), do: Descr.boolean()
  defp builtin_type("boolean"), do: Descr.boolean()
  defp builtin_type("int"), do: Descr.integer()
  defp builtin_type("integer"), do: Descr.integer()
  defp builtin_type("float"), do: Descr.float()
  defp builtin_type("number"), do: Descr.opt_union(Descr.integer(), Descr.float())
  defp builtin_type("binary"), do: Descr.binary()
  defp builtin_type("bitstring"), do: Descr.bitstring()
  defp builtin_type("pid"), do: Descr.pid()
  defp builtin_type("port"), do: Descr.port()
  defp builtin_type("reference"), do: Descr.reference()
  defp builtin_type("tuple"), do: Descr.tuple()
  defp builtin_type("map"), do: Descr.open_map()
  defp builtin_type("record"), do: Descr.open_map()
  defp builtin_type("arrow"), do: Descr.fun()
  defp builtin_type("fun"), do: Descr.fun()
  defp builtin_type("function"), do: Descr.fun()
  defp builtin_type("empty_map"), do: Descr.empty_map()
  defp builtin_type("empty_list"), do: Descr.empty_list()

  defp builtin_type("list"),
    do:
      Descr.opt_union(Descr.empty_list(), Descr.non_empty_list(Descr.term(), Descr.empty_list()))

  defp builtin_type("not_set"), do: Descr.not_set()
  defp builtin_type(_), do: nil

  defp identifier_atom(id) do
    if alias_identifier?(id) do
      id
      |> String.split(".")
      |> Module.concat()
    else
      String.to_atom(id)
    end
  end

  defp alias_identifier?(id) do
    id
    |> String.split(".")
    |> Enum.all?(fn
      <<first, _rest::binary>> -> first in ?A..?Z
      "" -> false
    end)
  end

  defp tuple_from_types(types), do: type(Descr.tuple(types))

  defp tuple(entries, tag \\ :closed) do
    types = Enum.map(entries, fn entry -> elem(as_type(entry), 1) end)
    descr = if tag == :open, do: Descr.open_tuple(types), else: Descr.tuple(types)
    {:tuple, entries, descr}
  end

  defp domain(entries) do
    types = Enum.map(entries, fn entry -> elem(as_type(entry), 1) end)
    {:domain, entries, Descr.tuple(types)}
  end

  defp type(type), do: {:type, type}

  defp as_type({:type, type}), do: {:ok, type}
  defp as_type({:tuple, _entries, type}), do: {:ok, type}
  defp as_type({:domain, _entries, type}), do: {:ok, type}

  defp function_type({:domain, entries, _type}, return_type) do
    types = Enum.map(entries, fn entry -> elem(as_type(entry), 1) end)
    type(Descr.fun(types, return_type))
  end

  defp function_type(left, return_type) do
    {:ok, left} = as_type(left)
    type(Descr.fun([left], return_type))
  end

  defp function_args({:domain, entries, _type}) do
    Enum.map(entries, fn entry -> elem(as_type(entry), 1) end)
  end

  defp function_args(type) do
    {:ok, type} = as_type(type)
    [type]
  end

  defp apply_type(fun, arg) do
    {:ok, fun} = as_type(fun)
    args = function_args(arg)

    case Descr.fun_apply(fun, args) do
      {:ok, result} ->
        type(result)

      :badfun ->
        error!("cannot apply non-function type #{Descr.to_quoted_string(fun)}")

      {:badarg, domain, _empty?} ->
        error!(
          "bad function argument #{application_args_to_string(args)}; expected #{Descr.to_quoted_string(domain)}"
        )

      {:badarity, arities} ->
        error!("bad function arity; expected one of #{inspect(arities)}")
    end
  end

  defp application_args_to_string([arg]), do: Descr.to_quoted_string(arg)

  defp application_args_to_string(args) do
    args
    |> Enum.map_join(", ", &Descr.to_quoted_string/1)
    |> then(&"(#{&1})")
  end

  defp project_map(map, key) do
    {:ok, map} = as_type(map)
    {:ok, key} = as_type(key)

    case map_access(map, key) do
      {:ok, result} ->
        type(result)

      :badmap ->
        error!("cannot project non-map type #{Descr.to_quoted_string(map)}")
    end
  end

  defp select_field(map, field) do
    {:ok, map} = as_type(map)
    key = String.to_atom(field)

    cond do
      Descr.empty?(map) ->
        type(Descr.none())

      true ->
        case Descr.map_fetch_key(map, key) do
          {_optional?, result} ->
            type(result)

          :badmap ->
            error!(
              "cannot select field #{inspect(key)} from non-map type #{Descr.to_quoted_string(map)}"
            )

          :badkey ->
            error!(
              "cannot select field #{inspect(key)} because it is not guaranteed on #{Descr.to_quoted_string(map)}"
            )
        end
    end
  end

  defp map_access(map, key) do
    cond do
      Descr.empty?(map) or Descr.empty?(key) ->
        {:ok, Descr.none()}

      true ->
        map_access_key(map, key, Descr.atom_fetch(key))
    end
  end

  defp map_access_key(map, _key, {:finite, atoms}) do
    Enum.reduce_while(atoms, {Descr.none(), false}, fn atom, {acc, include_nil?} ->
      case Descr.map_fetch_key(map, atom) do
        {optional?, value} ->
          {:cont, {Descr.opt_union(acc, value), include_nil? or optional?}}

        :badkey ->
          case Descr.map_get(map, Descr.atom([atom])) do
            {:ok, value} -> {:cont, {Descr.opt_union(acc, value), true}}
            :error -> {:cont, {acc, true}}
            :badmap -> {:halt, :badmap}
          end

        :badmap ->
          {:halt, :badmap}
      end
    end)
    |> case do
      :badmap -> :badmap
      {value, true} -> {:ok, Descr.opt_union(value, nil_type())}
      {value, false} -> {:ok, value}
    end
  end

  defp map_access_key(map, key, _atom_fetch) do
    case Descr.map_get(map, key) do
      {:ok, value} -> {:ok, Descr.opt_union(value, nil_type())}
      :error -> {:ok, nil_type()}
      :badmap -> :badmap
    end
  end

  defp nil_type, do: Descr.atom([nil])

  defp parse_precise_command("precise?", _state),
    do: error!("expected a pattern head after `precise?`")

  defp parse_precise_command("precise?" <> head, state) do
    head = String.trim(head)
    {patterns, guards} = parse_precise_head(head)
    {{:boolean, precise?(patterns, guards)}, state}
  end

  defp parse_precise_head(""), do: error!("expected a pattern head after `precise?`")

  defp parse_precise_head(head) do
    source = "fn " <> head <> " -> :ok end"

    with {:ok, fun} <- Code.string_to_quoted(source),
         {:ok, fun} <- expand_precise_fun(fun) do
      case fun do
        {:fn, _, [{:->, _, [heads, _body]}]} when is_list(heads) ->
          extract_precise_head(heads)

        _ ->
          error!("expected a single pattern head")
      end
    else
      {:error, {_line, message, token}} ->
        error!("invalid pattern head: #{message}#{format_parse_token(token)}")

      {:error, message} ->
        error!("invalid pattern head: #{message}")
    end
  end

  defp expand_precise_fun({:fn, fn_meta, [{:->, arrow_meta, [heads, _body]}]})
       when is_list(heads) do
    body = precise_body(heads)
    fun = {:fn, fn_meta, [{:->, arrow_meta, [heads, body]}]}
    env = __ENV__
    {:ok, elem(:elixir_expand.expand(fun, :elixir_env.env_to_ex(env), env), 0)}
  rescue
    exception ->
      {:error, Exception.message(exception)}
  catch
    _kind, value ->
      {:error, inspect(value)}
  end

  defp expand_precise_fun(_fun), do: {:error, "expected a single pattern head"}

  defp precise_body(heads) do
    {_heads, vars} =
      Macro.prewalk(heads, [], fn
        {:"::", _, [left, _right]}, acc ->
          {left, acc}

        {name, _, context} = var, acc when is_atom(context) and name != :_ ->
          {var, [var | acc]}

        node, acc ->
          {node, acc}
      end)

    vars =
      vars
      |> Enum.reverse()
      |> Enum.uniq_by(fn {name, _meta, context} -> {name, context} end)

    {:{}, [], vars}
  end

  defp extract_precise_head([{:when, _, args}]) do
    {patterns, [guard]} = Enum.split(args, -1)
    {patterns, flatten_when(guard)}
  end

  defp extract_precise_head(patterns), do: {patterns, [true]}

  defp flatten_when({:when, _meta, [left, right]}), do: [left | flatten_when(right)]
  defp flatten_when(other), do: [other]

  defp precise?(patterns, guards) do
    handler = fn _meta, fun_arity, _stack, _context ->
      raise "no local lookup for: #{inspect(fun_arity)}"
    end

    stack = Types.stack(:static, "types_repl", __MODULE__, {:precise?, 0}, [], nil, handler)
    expected = Enum.map(patterns, fn _ -> Descr.dynamic() end)
    previous = Pattern.init_previous()
    tag = {:fn, patterns}

    {_trees, precise?, _args_types, _previous, _context} =
      Pattern.of_head(patterns, guards, expected, previous, tag, [], stack, Types.context())

    precise?
  rescue
    exception ->
      error!("precision check failed: #{Exception.message(exception)}")
  end

  defp format_parse_token(""), do: ""
  defp format_parse_token(token), do: " near #{inspect(token)}"

  defp format_tally_solutions([]), do: "no solutions"

  defp format_tally_solutions(solutions) do
    solutions
    |> Enum.map(&format_tally_solution/1)
    |> Enum.join("\n")
  end

  defp format_tally_solution(solution) when map_size(solution) == 0, do: "[]"

  defp format_tally_solution(solution) do
    entries =
      solution
      |> Enum.sort_by(fn {variable, _type} -> Descr.to_quoted_string(variable) end)
      |> Enum.map(fn {variable, type} ->
        "#{Descr.to_quoted_string(variable)}: #{Descr.to_quoted_string(type)}"
      end)

    last_index = length(entries) - 1

    body =
      entries
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {entry, index} ->
        suffix = if index == last_index, do: "", else: " ;"
        "  #{entry}#{suffix}"
      end)

    "[\n#{body}\n]"
  end

  defp expect_end!([:eof]), do: :ok
  defp expect_end!([token | _]), do: error!("unexpected token #{format_token(token)}")

  defp tokenize(input) do
    input
    |> String.to_charlist()
    |> tokenize([])
    |> Enum.reverse()
    |> Kernel.++([:eof])
  end

  defp tokenize([], acc), do: acc

  defp tokenize([char | rest], acc) when char in [?\s, ?\t, ?\r, ?\n] do
    tokenize(rest, acc)
  end

  defp tokenize([?# | rest], acc) do
    rest
    |> Enum.drop_while(&(&1 != ?\n))
    |> tokenize(acc)
  end

  defp tokenize([?;, ?; | rest], acc), do: tokenize(rest, acc)
  defp tokenize([?-, ?> | rest], acc), do: tokenize(rest, [:arrow | acc])
  defp tokenize([?<, ?=, ?~ | rest], acc), do: tokenize(rest, [:consistent_subtype | acc])
  defp tokenize([?<, ?~, ?= | rest], acc), do: tokenize(rest, [:precision | acc])
  defp tokenize([?<, ?~ | rest], acc), do: tokenize(rest, [:precision | acc])
  defp tokenize([?<, ?= | rest], acc), do: tokenize(rest, [:lte | acc])
  defp tokenize([?>, ?= | rest], acc), do: tokenize(rest, [:gte | acc])
  defp tokenize([?=, ?> | rest], acc), do: tokenize(rest, [:fat_arrow | acc])
  defp tokenize([?., ?., ?. | rest], acc), do: tokenize(rest, [:ellipsis | acc])
  defp tokenize([?., ?. | rest], acc), do: tokenize(rest, [:dotdot | acc])
  defp tokenize([?%, ?{ | rest], acc), do: tokenize(rest, [:percent_lbrace | acc])
  defp tokenize([?( | rest], acc), do: tokenize(rest, [:lparen | acc])
  defp tokenize([?) | rest], acc), do: tokenize(rest, [:rparen | acc])
  defp tokenize([?{ | rest], acc), do: tokenize(rest, [:lbrace | acc])
  defp tokenize([?} | rest], acc), do: tokenize(rest, [:rbrace | acc])
  defp tokenize([?[ | rest], acc), do: tokenize(rest, [:lbracket | acc])
  defp tokenize([?] | rest], acc), do: tokenize(rest, [:rbracket | acc])
  defp tokenize([?, | rest], acc), do: tokenize(rest, [:comma | acc])
  defp tokenize([?; | rest], acc), do: tokenize(rest, [:semicolon | acc])
  defp tokenize([?: | rest], acc), do: tokenize_colon(rest, acc)
  defp tokenize([?| | rest], acc), do: tokenize(rest, [:bar | acc])
  defp tokenize([?& | rest], acc), do: tokenize(rest, [:amp | acc])
  defp tokenize([?\\ | rest], acc), do: tokenize(rest, [:backslash | acc])
  defp tokenize([?~, ?<, ?= | rest], acc), do: tokenize(rest, [:compatible | acc])
  defp tokenize([?~ | rest], acc), do: tokenize(rest, [:tilde | acc])
  defp tokenize([?= | rest], acc), do: tokenize(rest, [:eq | acc])
  defp tokenize([?? | rest], acc), do: tokenize(rest, [:question | acc])
  defp tokenize([?. | rest], acc), do: tokenize(rest, [:dot | acc])

  defp tokenize([?- | rest] = chars, acc) do
    case rest do
      [digit | _] when digit in ?0..?9 -> tokenize_integer(chars, acc)
      _ -> error!("unexpected character `-`")
    end
  end

  defp tokenize([digit | _] = chars, acc) when digit in ?0..?9 do
    tokenize_integer(chars, acc)
  end

  defp tokenize([char | _] = chars, acc) when char in ?a..?z or char in ?A..?Z or char == ?_ do
    {id, rest} = take_identifier(chars, [])
    {id, rest} = take_alias_segments(id, rest)
    tokenize(rest, [identifier_token(to_string(id)) | acc])
  end

  defp tokenize([char | _], _acc) do
    error!("unexpected character #{inspect(<<char::utf8>>)}")
  end

  defp tokenize_colon([char | _] = chars, acc)
       when char in ?a..?z or char in ?A..?Z or char == ?_ do
    {id, rest} = take_identifier(chars, [])
    tokenize(rest, [{:atom, id |> to_string() |> String.to_atom()} | acc])
  end

  defp tokenize_colon(rest, acc), do: tokenize(rest, [:colon | acc])

  defp tokenize_integer(chars, acc) do
    {number, rest} = take_integer(chars, [])
    {integer, ""} = number |> to_string() |> Integer.parse()
    tokenize(rest, [{:integer, integer} | acc])
  end

  defp take_integer([?- | rest], []), do: take_integer(rest, [?-])
  defp take_integer([char | rest], acc) when char in ?0..?9, do: take_integer(rest, [char | acc])
  defp take_integer(rest, acc), do: {Enum.reverse(acc), rest}

  defp take_identifier([char | rest], acc)
       when char in ?a..?z or char in ?A..?Z or char in ?0..?9 or char == ?_ do
    take_identifier(rest, [char | acc])
  end

  defp take_identifier(rest, acc), do: {Enum.reverse(acc), rest}

  defp take_alias_segments(id, rest) do
    if alias_segment?(id) do
      do_take_alias_segments(id, rest)
    else
      {id, rest}
    end
  end

  defp do_take_alias_segments(id, [?. | rest] = chars) do
    case rest do
      [char | _] when char in ?A..?Z ->
        {segment, rest} = take_identifier(rest, [])

        if alias_segment?(segment) do
          do_take_alias_segments(id ++ [?. | segment], rest)
        else
          {id, chars}
        end

      _ ->
        {id, chars}
    end
  end

  defp do_take_alias_segments(id, rest), do: {id, rest}

  defp alias_segment?([first | _]), do: first in ?A..?Z
  defp alias_segment?([]), do: false

  defp identifier_token("and"), do: :and
  defp identifier_token("or"), do: :or
  defp identifier_token("not"), do: :not
  defp identifier_token("when"), do: :when
  defp identifier_token(id), do: {:id, id}

  defp format_token(:eof), do: "end of input"
  defp format_token(:lparen), do: "`(`"
  defp format_token(:rparen), do: "`)`"
  defp format_token(:lbrace), do: "`{`"
  defp format_token(:rbrace), do: "`}`"
  defp format_token(:lbracket), do: "`[`"
  defp format_token(:rbracket), do: "`]`"
  defp format_token(:percent_lbrace), do: "`%{`"
  defp format_token(:comma), do: "`,`"
  defp format_token(:semicolon), do: "`;`"
  defp format_token(:colon), do: "`:`"
  defp format_token(:bar), do: "`|`"
  defp format_token(:amp), do: "`&`"
  defp format_token(:backslash), do: "`\\`"
  defp format_token(:tilde), do: "`~`"
  defp format_token(:or), do: "`or`"
  defp format_token(:and), do: "`and`"
  defp format_token(:not), do: "`not`"
  defp format_token(:when), do: "`when`"
  defp format_token(:arrow), do: "`->`"
  defp format_token(:lte), do: "`<=`"
  defp format_token(:gte), do: "`>=`"
  defp format_token(:consistent_subtype), do: "`<=~`"
  defp format_token(:precision), do: "`<~`"
  defp format_token(:compatible), do: "`~<=`"
  defp format_token(:eq), do: "`=`"
  defp format_token(:fat_arrow), do: "`=>`"
  defp format_token(:dot), do: "`.`"
  defp format_token(:dotdot), do: "`..`"
  defp format_token(:ellipsis), do: "`...`"
  defp format_token(:question), do: "`?`"
  defp format_token({:id, id}), do: "identifier #{inspect(id)}"
  defp format_token({:atom, atom}), do: "atom #{inspect(atom)}"
  defp format_token({:integer, integer}), do: "integer #{integer}"

  defp error!(message), do: throw({:repl_error, message})
end

defmodule Module.Types.Repl.CLI do
  @moduledoc false

  alias Module.Types.Repl

  def main(args) do
    case args do
      ["--help"] ->
        IO.write(Repl.help())

      ["--eval", input] ->
        eval_or_halt(input, Repl.new())

      [] ->
        loop(Repl.new(), "")

      files ->
        files
        |> Enum.reduce(Repl.new(), fn file, state ->
          file
          |> File.read!()
          |> eval_or_halt(state)
        end)
    end
  end

  defp loop(state, buffer) do
    prompt = if String.trim(buffer) == "", do: "> ", else: "... "

    case IO.gets(prompt) do
      :eof ->
        :ok

      {:error, reason} ->
        IO.puts(:stderr, "error reading input: #{:file.format_error(reason)}")
        System.halt(1)

      line ->
        buffer = buffer <> line
        {commands, rest} = Repl.split_commands(buffer)
        state = eval_commands(commands, state)
        loop(state, rest)
    end
  end

  defp eval_or_halt(input, state) do
    case Repl.eval(input, state) do
      {:ok, output, state} ->
        Enum.each(output, &IO.puts/1)
        state

      {:error, message, _state} ->
        IO.puts(:stderr, "error: #{message}")
        System.halt(1)
    end
  end

  defp eval_commands(commands, state) do
    Enum.reduce(commands, state, fn command, state ->
      case Repl.eval_command(command, state) do
        {:ok, nil, state} ->
          state

        {:ok, output, state} ->
          IO.puts(output)
          state

        {:error, message, _state} ->
          IO.puts(:stderr, "error: #{message}")
          state
      end
    end)
  end
end
