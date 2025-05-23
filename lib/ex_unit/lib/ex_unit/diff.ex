# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

defmodule ExUnit.Diff do
  @moduledoc false

  # A Diff struct and functions.
  #
  # The Diff struct contains the fields `:equivalent?`, `:left`, `:right`.
  # The `:equivalent?` field represents if the `:left` and `:right` side are
  # equivalents and contain no diffs. The `:left` and `:right` represent the
  # sides of the comparison as ASTs.
  #
  # The ASTs may be wrapped in blocks with two special metas:
  #
  #   * `:diff` - when `true`, the AST inside of it has no equivalent
  #     on the other side and should be rendered in a different color
  #
  #   * `:delimiter` - that particular block should be rendered with
  #     a delimiter
  #
  # Given blocks are do not appear on the left side or right, it is
  # safe to perform such wrapping.

  alias Inspect.Algebra

  defstruct equivalent?: true,
            left: nil,
            right: nil

  @doc """
  Returns the diff between `left` and `right` and env after the comparison.

  The `left` side can be a literal or an AST, the `right` should always be a
  value. The `context` should be `{:match, pins}` for pattern matching and
  `==` and `===` for comparison cases.
  """
  def compute(left, right, context) do
    diff(left, right, context_to_env(context))
  end

  defp context_to_env({:match, pins}),
    do: %{pins: Map.new(pins), context: :match, current_vars: %{}, hints: []}

  defp context_to_env(op) when op in [:==, :===],
    do: %{pins: %{}, context: op, current_vars: %{}, hints: []}

  # Main entry point for recursive diff

  defp diff(left, right, %{context: :match} = env) do
    case left do
      {_, [original: original] ++ _, _} ->
        diff_quoted(original, right, left, env)

      _ ->
        diff_quoted(left, right, nil, env)
    end
  end

  defp diff(left, right, env), do: diff_value(left, right, env)

  # diff quoted

  defp diff_quoted({:_, _, context} = left, right, _expanded, env) when is_atom(context) do
    diff_right = escape(right)
    diff = %__MODULE__{equivalent?: true, left: left, right: diff_right}
    {diff, env}
  end

  defp diff_quoted({:^, _, [{name, _, context}]} = left, right, _expanded, env)
       when is_atom(name) and is_atom(context) do
    diff_pin(left, right, env)
  end

  defp diff_quoted({name, _, context} = left, right, _expanded, env)
       when is_atom(name) and is_atom(context) and
              name not in [:__MODULE__, :__DIR__, :__STACKTRACE__, :__ENV__, :__CALLER__] do
    diff_var(left, right, env)
  end

  defp diff_quoted({:-, _, [number]}, right, _expanded, env) when is_number(number) do
    diff_quoted(-number, right, nil, env)
  end

  defp diff_quoted({:+, _, [number]}, right, _expanded, env) when is_number(number) do
    diff_quoted(number, right, nil, env)
  end

  defp diff_quoted({:++, meta, [prefix, suffix]}, right, _expanded, env) when is_list(right) do
    diff_maybe_improper_list({:++, meta, [prefix, suffix]}, right, env)
  end

  defp diff_quoted({:{}, _, left}, right, _expanded, env) when is_tuple(right) do
    diff_tuple(left, Tuple.to_list(right), env)
  end

  defp diff_quoted({_, _} = left, right, _expanded, env) when is_tuple(right) do
    diff_tuple(Tuple.to_list(left), Tuple.to_list(right), env)
  end

  defp diff_quoted({:%, _, [struct, {:%{}, _, kw}]}, %{} = right, _expanded, env)
       when is_list(kw) do
    diff_quoted_struct([__struct__: struct] ++ kw, right, env)
  end

  defp diff_quoted({:%{}, _, kw}, %{} = right, _expanded, env) when is_list(kw) do
    diff_quoted_struct(kw, right, env)
  end

  defp diff_quoted({:<>, _, [literal, _]} = left, right, _expanded, env)
       when is_binary(literal) and is_binary(right) do
    diff_string_concat(left, right, env)
  end

  defp diff_quoted({:when, _, [_, _]} = left, right, _expanded, env) do
    diff_guard(left, right, env)
  end

  defp diff_quoted({_, _, _} = left, right, expanded, env) when expanded != nil do
    expanded = Macro.update_meta(expanded, &Keyword.delete(&1, :original))
    {diff, post_env} = diff(expanded, right, env)
    diff_left = update_diff_meta(left, !diff.equivalent?)
    {%{diff | left: diff_left}, post_env}
  end

  defp diff_quoted(left, right, _expanded, env) when is_list(left) and is_list(right) do
    diff_maybe_list(left, right, env)
  end

  defp diff_quoted(left, right, _expanded, env)
       when is_atom(left) or is_number(left) or is_reference(left) or
              is_pid(left) or is_function(left) or is_binary(left) do
    diff_value(left, right, env)
  end

  defp diff_quoted(left, right, _expanded, %{context: :match} = env) do
    diff_left = update_diff_meta(left, true)
    diff_right = escape(right) |> update_diff_meta(true)
    diff = %__MODULE__{equivalent?: false, left: diff_left, right: diff_right}
    {diff, env}
  end

  ## diff_value

  defp diff_value(literal, literal, env)
       when is_atom(literal) or is_number(literal) or is_reference(literal) or
              is_pid(literal) or is_function(literal) do
    {%__MODULE__{equivalent?: true, left: literal, right: literal}, env}
  end

  defp diff_value(left, right, %{context: :==} = env) when left == right and is_number(left) do
    {%__MODULE__{equivalent?: true, left: left, right: right}, env}
  end

  defp diff_value(left, right, env) when is_number(left) and is_number(right) do
    diff_number(left, right, env)
  end

  defp diff_value(left, right, env) when is_list(left) and is_list(right) do
    diff_maybe_list(left, right, env)
  end

  defp diff_value(left, right, env) when is_tuple(left) and is_tuple(right) do
    diff_tuple(Tuple.to_list(left), Tuple.to_list(right), env)
  end

  defp diff_value(%left_struct{} = left, %right_struct{} = right, env) do
    diff_struct(
      left,
      Map.to_list(left),
      right,
      left_struct,
      right_struct,
      env
    )
  end

  defp diff_value(%{} = left, %{} = right, env) do
    diff_map(Map.to_list(left), right, maybe_struct(left), maybe_struct(right), env)
  end

  defp diff_value(left, right, env) when is_binary(left) and is_binary(right) do
    diff_string(left, right, ?", env)
  end

  defp diff_value(left, right, env) when is_function(left) and is_function(right) do
    # If they are local functions in the same module and same name,
    # then they have different environment, which we compare.
    if Function.info(left, :type) == {:type, :local} and
         Function.info(right, :type) == {:type, :local} and
         Function.info(left, :module) == Function.info(right, :module) and
         Function.info(left, :new_uniq) == Function.info(right, :new_uniq) and
         Function.info(left, :new_index) == Function.info(right, :new_index) do
      {:env, left_env} = Function.info(left, :env)
      {:env, right_env} = Function.info(right, :env)
      {diff, env} = diff_maybe_improper_list(left_env, right_env, env)

      diff = %{
        diff
        | left: %{custom: &function_env_to_algebra(left, diff.left, &1)},
          right: %{custom: &function_env_to_algebra(right, diff.right, &1)}
      }

      {diff, env}
    else
      non_recursive_diff_value(left, right, env)
    end
  end

  defp diff_value(left, right, env) do
    non_recursive_diff_value(left, right, env)
  end

  defp non_recursive_diff_value(left, right, env) do
    diff_left = escape(left) |> update_diff_meta(true)
    diff_right = escape(right) |> update_diff_meta(true)
    diff = %__MODULE__{equivalent?: false, left: diff_left, right: diff_right}
    {diff, env}
  end

  # Guards

  defp diff_guard({:when, _, [expression, clause]}, right, env) do
    {diff, post_env} = diff_quoted(expression, right, nil, env)

    {guard_clause, guard_equivalent?} =
      if diff.equivalent? do
        bindings = Map.merge(post_env.pins, post_env.current_vars)
        diff_guard_clause(clause, bindings)
      else
        {clause, false}
      end

    diff = %{
      diff
      | left: {:when, [], [diff.left, guard_clause]},
        equivalent?: guard_equivalent?
    }

    {diff, post_env}
  end

  defp diff_guard_clause(quoted, bindings) do
    case original_or_current(quoted) do
      {op, _, [clause1, clause2]} when op in [:and, :or, :when] ->
        {diff_clause1, clause1_equivalent?} = diff_guard_clause(clause1, bindings)
        {diff_clause2, clause2_equivalent?} = diff_guard_clause(clause2, bindings)

        equivalent? =
          case op do
            :and -> clause1_equivalent? and clause2_equivalent?
            _other -> clause1_equivalent? or clause2_equivalent?
          end

        diff = {op, [], [diff_clause1, diff_clause2]}
        {diff, equivalent?}

      _ ->
        {original, valid?} =
          Macro.postwalk(quoted, true, fn
            {_, [original: original] ++ _, _}, valid? ->
              {original, valid?}

            {var, _, context} = expr, valid? when is_atom(var) and is_atom(context) ->
              if Map.has_key?(bindings, var_context(expr)) do
                {expr, valid?}
              else
                {expr, false}
              end

            other, valid? ->
              {other, valid?}
          end)

        if valid? do
          {equivalent?, _bindings} = Code.eval_quoted(quoted, Map.to_list(bindings))
          {update_diff_meta(original, equivalent? != true), equivalent? == true}
        else
          {original, false}
        end
    end
  end

  defp original_or_current({_, [original: original] ++ _, _}), do: original
  defp original_or_current(current), do: current

  # Pins

  defp diff_pin({:^, _, [var]} = pin, right, %{pins: pins} = env) do
    identifier = var_context(var)
    %{^identifier => pin_value} = pins
    {diff, post_env} = diff_value(pin_value, right, %{env | context: :===})

    diff_left = update_diff_meta(pin, not diff.equivalent?)
    {%{diff | left: diff_left}, %{post_env | context: :match}}
  end

  # Vars

  defp diff_var(left, right, env) do
    identifier = var_context(left)

    case env.current_vars do
      %{^identifier => ^right} ->
        diff_right = escape(right)
        diff = %__MODULE__{equivalent?: true, left: left, right: diff_right}
        {diff, env}

      %{^identifier => _} ->
        diff_left = update_diff_meta(left, true)
        diff_right = escape(right) |> update_diff_meta(true)
        diff = %__MODULE__{equivalent?: false, left: diff_left, right: diff_right}
        {diff, env}

      current_vars = %{} ->
        updated_vars = Map.put(current_vars, identifier, right)
        diff_right = escape(right)
        diff = %__MODULE__{equivalent?: true, left: left, right: diff_right}
        {diff, %{env | current_vars: updated_vars}}
    end
  end

  # Tuples

  defp diff_tuple(list_left, list_right, env) do
    diff_tuple(list_left, list_right, true, [], [], env)
  end

  defp diff_tuple([left | tleft], [right | tright], acc_equivalent?, acc_left, acc_right, env) do
    {diff, env} = diff(left, right, env)
    acc_equivalent? = acc_equivalent? and diff.equivalent?
    acc_left = [diff.left | acc_left]
    acc_right = [diff.right | acc_right]
    diff_tuple(tleft, tright, acc_equivalent?, acc_left, acc_right, env)
  end

  defp diff_tuple(remaining_left, remaining_right, acc_equivalent?, acc_left, acc_right, env) do
    remaining_left =
      Enum.map(remaining_left, &(&1 |> maybe_escape(env) |> update_diff_meta(true)))

    remaining_right = Enum.map(remaining_right, &(&1 |> escape() |> update_diff_meta(true)))

    equivalent? = acc_equivalent? and remaining_left == [] and remaining_right == []
    diff_left = {:{}, [], Enum.reverse(acc_left, remaining_left)}
    diff_right = {:{}, [], Enum.reverse(acc_right, remaining_right)}
    {%__MODULE__{equivalent?: equivalent?, left: diff_left, right: diff_right}, env}
  end

  # Lists

  defp diff_maybe_list([], [], env) do
    {%__MODULE__{equivalent?: true, left: [], right: []}, env}
  end

  defp diff_maybe_list(left, right, env) do
    if List.ascii_printable?(left) and List.ascii_printable?(right) do
      {diff, env} = diff_string(List.to_string(left), List.to_string(right), ?", env)

      diff = %{
        diff
        | left: %{custom: &charlist_to_algebra(diff.left, &1)},
          right: %{custom: &charlist_to_algebra(diff.right, &1)}
      }

      {diff, env}
    else
      diff_maybe_improper_list(left, right, env)
    end
  end

  # Compare two lists, removing all the operators (`|` and `++`) from the left
  # side before and adding them back in the end. Improper lists on the left side
  # are handled as quoted expressions. Improper lists on the right side are
  # handled as runtime improper lists.
  defp diff_maybe_improper_list(left, right, env) do
    {parsed_left, improper_left, operators_left, length_left} =
      split_left_list(left, 0, env.context)

    element_limit = if improper_left == [], do: -1, else: length_left
    {parsed_right, improper_right} = split_right_list(right, element_limit, [])

    {parsed_diff, parsed_post_env} = myers_difference_list(parsed_left, parsed_right, env)

    {improper_diff, improper_post_env} =
      diff_improper(improper_left, improper_right, parsed_post_env)

    diff =
      merge_diff(parsed_diff, improper_diff, fn left1, left2, right1, right2 ->
        improper_left =
          cond do
            improper_left != [] -> {:improper, left2}
            improper_right != [] -> :tail
            true -> :nothing
          end

        left = rebuild_left_list(left1, improper_left, operators_left, env)
        right = rebuild_right_list(right1, right2)
        {left, right}
      end)

    {diff, improper_post_env}
  end

  defp diff_improper([], right, env) when is_list(right) do
    equivalent? = right == []
    right = right |> escape() |> update_diff_meta(not equivalent?)
    {%__MODULE__{equivalent?: equivalent?, right: right, left: []}, env}
  end

  defp diff_improper(left, right, env) do
    diff(left, right, env)
  end

  defp split_right_list([head | tail], length, acc) when length != 0,
    do: split_right_list(tail, length - 1, [head | acc])

  defp split_right_list(rest, _length, acc),
    do: {Enum.reverse(acc), rest}

  defp rebuild_right_list(left, right) do
    left = Enum.reverse(left)

    case extract_diff_meta(right) do
      # Outer was escaped. Copy its diff? to its inner element and potentially escape it.
      {{unescaped}, diff?} ->
        rebuild_maybe_improper(unescaped, left, &(&1 |> escape() |> update_diff_meta(diff?)))

      # We have a proper list, if there are any diffs, they will be inside, so copy as is.
      {[_ | _] = list, false} ->
        rebuild_maybe_improper(list, left, & &1)

      # The right itself is improper, so just add it as is.
      {_, _} ->
        rebuild_maybe_improper(right, left, & &1)
    end
  end

  defp rebuild_maybe_improper([head | tail], acc, fun),
    do: rebuild_maybe_improper(tail, [fun.(head) | acc], fun)

  defp rebuild_maybe_improper([], acc, _fun),
    do: Enum.reverse(acc)

  defp rebuild_maybe_improper(other, [prev | acc], fun),
    do: Enum.reverse([{:|, [], [prev, fun.(other)]} | acc])

  defp split_left_list([], _index, _context) do
    {[], [], nil, 0}
  end

  defp split_left_list({:++, _, [left, right]}, _index, :match) do
    {parsed_left, [], operators_left, length_left} = split_left_list(left, 0, :match)

    case split_left_list(right, 0, :match) do
      {:improper, improper} ->
        operators = {:++, length_left, [operators_left, nil]}
        {parsed_left, improper, operators, length_left}

      {parsed_right, improper_right, operators_right, length_right} ->
        operators = {:++, length_left, [operators_left, operators_right]}
        length = length_right + length_left
        {parsed_left ++ parsed_right, improper_right, operators, length}
    end
  end

  defp split_left_list([{:|, _, [head, tail]}], index, :match) do
    case split_left_list(tail, 0, :match) do
      {:improper, improper} ->
        operator = {:|, index, [nil]}
        {[head], improper, operator, 1}

      {parsed_tail, improper_tail, operators_tail, length_tail} ->
        operators = {:|, index, [operators_tail]}
        {[head | parsed_tail], improper_tail, operators, length_tail + 1}
    end
  end

  defp split_left_list([head | tail], index, context) do
    case split_left_list(tail, index + 1, context) do
      {:improper, improper} ->
        operator = {:|, index, [nil]}
        {[head], improper, operator, 1}

      {parsed_tail, improper_tail, operators_tail, length_tail} ->
        {[head | parsed_tail], improper_tail, operators_tail, length_tail + 1}
    end
  end

  defp split_left_list(element, _index, _) do
    {:improper, element}
  end

  defp rebuild_left_list([], {:improper, improper}, _operators = nil, _env), do: improper
  defp rebuild_left_list(list, _, _operators = nil, _env), do: list

  defp rebuild_left_list(list, :tail, {:|, index, [operators]}, env) do
    {left, [head | tail]} = Enum.split(list, index)
    rebuilt_tail = rebuild_left_list(tail, :nothing, operators, env)
    rebuilt_tail = rebuilt_tail |> update_diff_meta(true)
    left ++ [{:|, [], [head, rebuilt_tail]}]
  end

  defp rebuild_left_list(list, improper, {:|, index, [operators]}, env) do
    {left, [head | tail]} = Enum.split(list, index)
    rebuilt_tail = rebuild_left_list(tail, improper, operators, env)
    left ++ [{:|, [], [head, rebuilt_tail]}]
  end

  defp rebuild_left_list(list, improper, {:++, index, operators}, env) do
    [operators_left, operators_right] = operators
    {left, right} = Enum.split(list, index)

    rebuilt_left = rebuild_left_list(left, :nothing, operators_left, env)
    rebuilt_right = rebuild_left_list(right, improper, operators_right, env)

    {:++, [], [rebuilt_left, rebuilt_right]}
  end

  defp myers_difference_list(left, right, env) do
    path = {0, left, right, {[], [], env}}
    find_diff(0, length(left) + length(right), [path])
  end

  defp find_diff(envelope, max, paths) do
    case each_diagonal(-envelope, envelope, paths, []) do
      {:done, {edit1, edit2, env}} ->
        list_script_to_diff(Enum.reverse(edit1), Enum.reverse(edit2), true, [], [], env)

      {:next, paths} ->
        find_diff(envelope + 1, max, paths)
    end
  end

  defp each_diagonal(diag, limit, _paths, next_paths) when diag > limit do
    {:next, Enum.reverse(next_paths)}
  end

  defp each_diagonal(diag, limit, paths, next_paths) do
    {path, rest} = proceed_path(diag, limit, paths)

    case follow_snake(path) do
      {:cont, path} -> each_diagonal(diag + 2, limit, rest, [path | next_paths])
      {:done, edits} -> {:done, edits}
    end
  end

  defp proceed_path(0, 0, [path]), do: {path, []}

  defp proceed_path(diag, limit, [path | _] = paths) when diag == -limit do
    {move_down(path), paths}
  end

  defp proceed_path(diag, limit, [path]) when diag == limit do
    {move_right(path), []}
  end

  defp proceed_path(_diag, _limit, [path1, path2 | rest]) do
    if elem(path1, 0) > elem(path2, 0) do
      {move_right(path1), [path2 | rest]}
    else
      {move_down(path2), [path2 | rest]}
    end
  end

  defp move_right({y, list1, [elem2 | rest2], {edit1, edit2, env}}) do
    {y, list1, rest2, {edit1, [{:ins, elem2} | edit2], env}}
  end

  defp move_right({y, list1, [], edits}) do
    {y, list1, [], edits}
  end

  defp move_down({y, [elem1 | rest1], list2, {edit1, edit2, env}}) do
    {y + 1, rest1, list2, {[{:del, elem1} | edit1], edit2, env}}
  end

  defp move_down({y, [], list2, edits}) do
    {y + 1, [], list2, edits}
  end

  defp follow_snake({y, [elem1 | rest1], [elem2 | rest2], {edit1, edit2, env}} = path) do
    {diff, post_env} = diff(elem1, elem2, env)

    if diff.equivalent? do
      new_edit1 = [{:eq, diff.left} | edit1]
      new_edit2 = [{:eq, diff.right} | edit2]

      follow_snake({y + 1, rest1, rest2, {new_edit1, new_edit2, post_env}})
    else
      {:cont, path}
    end
  end

  defp follow_snake({_y, [], [], edits}) do
    {:done, edits}
  end

  defp follow_snake(path) do
    {:cont, path}
  end

  defp list_script_to_diff([], [], equivalent?, left, right, env) do
    diff = %__MODULE__{
      equivalent?: equivalent?,
      left: Enum.reverse(left),
      right: Enum.reverse(right)
    }

    {diff, env}
  end

  defp list_script_to_diff(
         [{:del, elem1} | rest1],
         [{:ins, elem2} | rest2],
         equivalent?,
         left,
         right,
         env
       ) do
    {diff, env} = diff(elem1, elem2, env)
    equivalent? = equivalent? and diff.equivalent?
    list_script_to_diff(rest1, rest2, equivalent?, [diff.left | left], [diff.right | right], env)
  end

  defp list_script_to_diff([{:del, elem1} | rest1], rest2, _, left, right, env) do
    diff_left = elem1 |> maybe_escape(env) |> update_diff_meta(true)
    list_script_to_diff(rest1, rest2, false, [diff_left | left], right, env)
  end

  defp list_script_to_diff(rest1, [{:ins, elem2} | rest2], _, left, right, env) do
    diff_right = elem2 |> escape() |> update_diff_meta(true)
    list_script_to_diff(rest1, rest2, false, left, [diff_right | right], env)
  end

  defp list_script_to_diff(
         [{:eq, elem1} | rest1],
         [{:eq, elem2} | rest2],
         equivalent?,
         left,
         right,
         env
       ) do
    list_script_to_diff(rest1, rest2, equivalent?, [elem1 | left], [elem2 | right], env)
  end

  # Maps

  # Compare items based on the keys of `left_items` and add the `:diff` meta to
  # the element that it wasn't able to compare.
  defp diff_map(left_items, right, struct1, struct2, env) do
    {equivalent?, left, right, env} = diff_map_by_key(left_items, right, env)
    left = build_map_or_struct(left, struct1)
    right = build_map_or_struct(right, struct2)
    {%__MODULE__{equivalent?: equivalent?, left: left, right: right}, env}
  end

  defp diff_map_by_key(items, right, env) do
    {acc_equivalent?, acc_left, acc_right, pending_left, pending_right, env} =
      Enum.reduce(items, {true, [], [], [], right, env}, fn
        {left_key, left_value},
        {acc_equivalent?, acc_left, acc_right, pending_left, pending_right, env} ->
          right_key = literal_key(left_key, env)

          case pending_right do
            %{^right_key => right_value} ->
              pending_right = Map.delete(pending_right, right_key)
              {diff, env} = diff(left_value, right_value, env)
              acc_equivalent? = acc_equivalent? and diff.equivalent?
              acc_left = [{maybe_escape(left_key, env), diff.left} | acc_left]
              acc_right = [{escape(right_key), diff.right} | acc_right]
              {acc_equivalent?, acc_left, acc_right, pending_left, pending_right, env}

            %{} ->
              pair = {maybe_escape(left_key, env), maybe_escape(left_value, env)}
              pair_diff = update_diff_meta(pair, true)
              {false, acc_left, acc_right, [pair_diff | pending_left], pending_right, env}
          end
      end)

    # It may be a struct, so make sure we convert it to a list before calling Enum
    pending_right = Map.to_list(pending_right)

    {pending_right, equivalent?} =
      if env.context == :match do
        {Enum.map(pending_right, &escape_pair/1), acc_equivalent?}
      else
        pending_right = Enum.map(pending_right, &(&1 |> escape_pair() |> update_diff_meta(true)))
        {pending_right, acc_equivalent? and pending_right == []}
      end

    left = Enum.sort(acc_left) ++ Enum.sort(pending_left)
    right = Enum.sort(acc_right) ++ Enum.sort(pending_right)

    {equivalent?, left, right, env}
  end

  defp literal_key({:^, _, [var]}, %{pins: pins}) do
    identifier = var_context(var)
    %{^identifier => pin_value} = pins
    pin_value
  end

  defp literal_key(literal, _env) do
    literal
  end

  # Structs

  defp diff_quoted_struct(kw, right, env) do
    if struct = struct_module(kw) do
      with true <- Macro.quoted_literal?(kw),
           {eval_kw, []} <- safe_eval(kw),
           {:ok, data} <- load_struct(struct, eval_kw) do
        diff_quoted_struct(data, kw, right, struct, env)
      else
        _ -> diff_map(kw, right, struct, maybe_struct(right), env)
      end
    else
      diff_map(kw, right, nil, maybe_struct(right), env)
    end
  end

  defp diff_quoted_struct(left, kw, %struct2{} = right, struct1, env) do
    diff_struct(left, kw, right, struct1, struct2, env)
  end

  defp diff_quoted_struct(_left, kw, right, struct1, env) do
    diff_map(kw, right, struct1, nil, env)
  end

  defp diff_struct(left, kw, right, struct1, struct2, env) do
    with true <- Inspect.impl_for(left) not in [Inspect.Any, Inspect.Map],
         {:ok, inspect_left} <- safe_inspect(left),
         {:ok, inspect_right} <- safe_inspect(right) do
      if inspect_left != inspect_right do
        diff_string(inspect_left, inspect_right, nil, env)
      else
        # If they are equivalent, still use their inspected form
        case diff_map(kw, right, struct1, struct2, env) do
          {%{equivalent?: true}, ctx} ->
            {%__MODULE__{equivalent?: true, left: left, right: right}, ctx}

          diff_ctx ->
            diff_ctx
        end
      end
    else
      _ -> diff_map(kw, right, struct1, struct2, env)
    end
  end

  defp struct_module(kw) do
    {struct, struct_kw} = Keyword.pop(kw, :__struct__)

    info =
      is_atom(struct) and struct != nil and
        Code.ensure_loaded?(struct) and function_exported?(struct, :__info__, 1) and
        struct.__info__(:struct)

    if info && Enum.all?(struct_kw, fn {k, _} -> Enum.any?(info, &(&1.field == k)) end) do
      struct
    end
  end

  defp load_struct(struct, kw) do
    {:ok, struct!(struct, kw)}
  rescue
    _ -> :error
  end

  defp maybe_struct(%name{}), do: name
  defp maybe_struct(_), do: nil

  defp build_map_or_struct(items, nil) do
    {:%{}, [], items}
  end

  defp build_map_or_struct(items, _struct) do
    {struct, items} = pop_struct(items, [])
    {:%, [], [struct, {:%{}, [], items}]}
  end

  defp pop_struct([{:__block__, meta, [{:__struct__, struct}]} | tail], acc),
    do: {{:__block__, meta, [struct]}, Enum.reverse(acc, tail)}

  defp pop_struct([{:__struct__, struct} | tail], acc),
    do: {struct, Enum.reverse(acc, tail)}

  defp pop_struct([head | rest], acc),
    do: pop_struct(rest, [head | acc])

  # Strings

  defp diff_string(left, right, delimiter, env) do
    {escaped_left, _} = Code.Identifier.escape(left, delimiter)
    {escaped_right, _} = Code.Identifier.escape(right, delimiter)
    left = IO.iodata_to_binary(escaped_left)
    right = IO.iodata_to_binary(escaped_right)

    cond do
      left == right ->
        {string_script_to_diff([eq: left], delimiter, true, [], []), env}

      diff_string?(left, right) ->
        diff =
          String.myers_difference(left, right)
          |> string_script_to_diff(delimiter, true, [], [])

        env =
          if String.equivalent?(left, right) do
            add_hint(env, :equivalent_but_different_strings)
          else
            env
          end

        {diff, env}

      true ->
        {string_script_to_diff([del: left, ins: right], delimiter, true, [], []), env}
    end
  end

  # Concat all the literals on `left` and split `right` based on the size of
  # that, comparing them and the remaining AST from `left` and the remaining
  # string from `right`.
  defp diff_string_concat(left, right, env) do
    {parsed_left, quoted, indexes, parsed_left_length} = parse_string(left)

    diff_string_concat(parsed_left, quoted, indexes, parsed_left_length, right, env)
  end

  defp diff_string_concat(left, nil, indexes, _left_length, right, env) do
    {diff, parsed_post_env} = diff_string(left, right, ?", env)
    left_diff = rebuild_concat_string(diff.left, nil, indexes)

    diff = %{diff | left: left_diff}
    {diff, parsed_post_env}
  end

  defp diff_string_concat(left, quoted, indexes, left_length, right, env) do
    {parsed_right, continue_right} = String.split_at(right, left_length)
    {parsed_diff, parsed_post_env} = diff_string(left, parsed_right, ?", env)
    {quoted_diff, quoted_post_env} = diff(quoted, continue_right, parsed_post_env)

    diff =
      merge_diff(parsed_diff, quoted_diff, fn left1, left2, right1, right2 ->
        new_left = rebuild_concat_string(left1, left2, indexes)
        new_right = rebuild_split_strings(right1, right2)
        {new_left, new_right}
      end)

    {diff, quoted_post_env}
  end

  defp diff_string?(left, right) do
    String.bag_distance(left, right) > 0.4
  end

  defp parse_string({:<>, _, [literal, rest]}) when is_binary(literal) do
    {parsed, quoted, indexes, parsed_length} = parse_string(rest)
    literal_length = String.length(literal)
    length = literal_length + parsed_length
    {literal <> parsed, quoted, [literal_length | indexes], length}
  end

  defp parse_string(literal) when is_binary(literal) do
    {literal, nil, [], String.length(literal)}
  end

  defp parse_string(pattern) do
    {"", pattern, [], 0}
  end

  defp rebuild_split_strings(left, "") do
    left
  end

  defp rebuild_split_strings(
         %{contents: left, delimiter: delimiter},
         %{contents: right, delimiter: delimiter}
       ) do
    %{contents: left ++ right, delimiter: delimiter}
  end

  defp rebuild_split_strings(%{contents: contents, delimiter: delimiter}, right) do
    {new_right, diff} = extract_diff_meta(right)
    %{contents: contents ++ [{diff, new_right}], delimiter: delimiter}
  end

  defp rebuild_concat_string(literal, nil, []) do
    literal
  end

  defp rebuild_concat_string(_literal, quoted, []) do
    quoted
  end

  defp rebuild_concat_string(literal, quoted, [index | rest]) do
    {next, continue} = next_concat_result(literal, index)
    rebuilt_right = rebuild_concat_string(continue, quoted, rest)
    {:<>, [], [next, rebuilt_right]}
  end

  defp next_concat_result(%{contents: contents, delimiter: delimiter}, index) do
    {next, continue} = next_concat_result(contents, index)
    {%{contents: next, delimiter: delimiter}, %{contents: continue, delimiter: delimiter}}
  end

  defp next_concat_result([{diff?, head} | tail], index) do
    length = String.length(head)

    cond do
      length > index ->
        {next, continue} = String.split_at(head, index)
        {[{diff?, next}], [{diff?, continue} | tail]}

      length < index ->
        {next, continue} = next_concat_result(tail, index - length)
        {[{diff?, head} | next], continue}

      true ->
        {[{diff?, head}], tail}
    end
  end

  defp string_script_to_diff([], delimiter, equivalent?, left, right) do
    left = %{delimiter: delimiter, contents: Enum.reverse(left)}
    right = %{delimiter: delimiter, contents: Enum.reverse(right)}
    %__MODULE__{equivalent?: equivalent?, left: left, right: right}
  end

  defp string_script_to_diff([{:eq, string} | tail], delimiter, equivalent?, left, right) do
    string_script_to_diff(
      tail,
      delimiter,
      equivalent?,
      [{false, string} | left],
      [{false, string} | right]
    )
  end

  defp string_script_to_diff([{:del, string} | tail], delimiter, _equivalent?, left, right) do
    string_script_to_diff(tail, delimiter, false, [{true, string} | left], right)
  end

  defp string_script_to_diff([{:ins, string} | tail], delimiter, _equivalent?, left, right) do
    string_script_to_diff(tail, delimiter, false, left, [{true, string} | right])
  end

  # Numbers

  defp diff_number(left, right, env) do
    diff_string(inspect(left), inspect(right), nil, env)
  end

  # Algebra

  @doc """
  Converts a diff to an algebra document.
  """
  def to_algebra(quoted, diff_wrapper) do
    wrap_on_diff(quoted, &safe_to_algebra/2, diff_wrapper)
  end

  defp safe_to_algebra(list, diff_wrapper) when is_list(list) do
    container_to_algebra("[", list, "]", diff_wrapper, select_list_item_algebra(list))
  end

  defp safe_to_algebra({op, _, [left, right]}, diff_wrapper)
       when op in [:<>, :++, :|, :when, :and, :or] do
    to_algebra(left, diff_wrapper)
    |> Algebra.concat(" #{op} ")
    |> Algebra.concat(to_algebra(right, diff_wrapper))
  end

  defp safe_to_algebra({:{}, _, args}, diff_wrapper) do
    container_to_algebra("{", args, "}", diff_wrapper, &to_algebra/2)
  end

  defp safe_to_algebra({a, b}, diff_wrapper) do
    container_to_algebra("{", [a, b], "}", diff_wrapper, &to_algebra/2)
  end

  defp safe_to_algebra({:%, _, [{:_, _, _}, {:%{}, _, list}]}, diff_wrapper) do
    open = Algebra.concat(["%", "_", "{"])
    container_to_algebra(open, list, "}", diff_wrapper, select_map_item_to_algebra(list))
  end

  defp safe_to_algebra({:%, _, [struct, {:%{}, _, list}]}, diff_wrapper) do
    open = Algebra.concat(["%", struct_to_algebra(struct, diff_wrapper), "{"])
    container_to_algebra(open, list, "}", diff_wrapper, select_map_item_to_algebra(list))
  end

  defp safe_to_algebra({:%{}, _, list}, diff_wrapper) do
    container_to_algebra("%{", list, "}", diff_wrapper, select_map_item_to_algebra(list))
  end

  defp safe_to_algebra({_, meta, args} = quoted, _diff_wrapper)
       when is_list(meta) and (is_list(args) or is_atom(args)) do
    Macro.to_string(quoted)
  end

  defp safe_to_algebra({escaped}, _diff_wrapper) do
    inspect(escaped)
  end

  # Custom encoding for delimiters+contents
  defp safe_to_algebra(%{delimiter: delimiter, contents: contents}, diff_wrapper) do
    content_docs =
      for {diff?, content} <- contents do
        if diff?, do: diff_wrapper.(content), else: content
      end

    if delimiter do
      delimiter = List.to_string([delimiter])
      Algebra.concat([delimiter, Algebra.concat(content_docs), delimiter])
    else
      Algebra.concat(content_docs)
    end
  end

  # Custom encoding for functions
  defp safe_to_algebra(%{custom: literal}, diff_wrapper) do
    literal.(diff_wrapper)
  end

  defp safe_to_algebra(literal, _diff_wrapper) do
    inspect(literal)
  end

  defp keyword_to_algebra(quoted, diff_wrapper) do
    wrap_on_diff(quoted, &safe_keyword_to_algebra/2, diff_wrapper)
  end

  defp safe_keyword_to_algebra({:{}, _, [key, value]}, diff_wrapper) do
    keyword_to_algebra({key, value}, diff_wrapper)
  end

  defp safe_keyword_to_algebra({key, value}, diff_wrapper) do
    key_to_algebra(key, diff_wrapper)
    |> Algebra.concat(" ")
    |> Algebra.concat(to_algebra(value, diff_wrapper))
  end

  defp key_to_algebra(quoted, diff_wrapper) do
    wrap_on_diff(quoted, &safe_key_to_algebra/2, diff_wrapper)
  end

  defp safe_key_to_algebra(key, _diff_wrapper) do
    Macro.inspect_atom(:key, key)
  end

  defp map_item_to_algebra(quoted, diff_wrapper) do
    wrap_on_diff(quoted, &safe_map_item_to_algebra/2, diff_wrapper)
  end

  defp safe_map_item_to_algebra({:{}, _, [key, value]}, diff_wrapper) do
    safe_map_item_to_algebra({key, value}, diff_wrapper)
  end

  defp safe_map_item_to_algebra({key, value}, diff_wrapper) do
    to_algebra(key, diff_wrapper)
    |> Algebra.concat(" => ")
    |> Algebra.concat(to_algebra(value, diff_wrapper))
  end

  defp container_to_algebra(open, list, close, diff_wrapper, item_to_algebra) do
    docs =
      list
      |> Enum.map(&item_to_algebra.(&1, diff_wrapper))
      |> Algebra.fold(&join_docs/2)

    open
    |> Algebra.glue("", docs)
    |> Algebra.nest(2)
    |> Algebra.glue("", close)
    |> Algebra.group()
  end

  defp join_docs(doc1, doc2) do
    doc1
    |> Algebra.concat(",")
    |> Algebra.glue(doc2)
  end

  defp struct_to_algebra(quoted, diff_wrapper) do
    wrap_on_diff(quoted, &safe_struct_to_algebra/2, diff_wrapper)
  end

  defp safe_struct_to_algebra({:^, _, _} = name, _diff_wrapper) do
    Macro.to_string(name)
  end

  defp safe_struct_to_algebra(name, _diff_wrapper) do
    Macro.inspect_atom(:literal, name)
  end

  defp select_list_item_algebra(list) do
    short? = Enum.all?(list, &keyword?/1)
    if short?, do: &keyword_to_algebra/2, else: &to_algebra/2
  end

  defp select_map_item_to_algebra(list) do
    short? = Enum.all?(list, &keyword?/1)
    if short?, do: &keyword_to_algebra/2, else: &map_item_to_algebra/2
  end

  defp wrap_on_diff(quoted, fun, wrapper) do
    case extract_diff_meta(quoted) do
      {expr, true} -> fun.(expr, & &1) |> wrapper.()
      {expr, false} -> fun.(expr, wrapper)
    end
  end

  defp charlist_to_algebra(%{contents: contents}, diff_wrapper) do
    content_doc =
      for {diff, content} <- contents do
        if diff, do: diff_wrapper.(content), else: content
      end

    Algebra.concat(["~c\"", Algebra.concat(content_doc), "\""])
  end

  defp function_env_to_algebra(function, ast, diff_wrapper) do
    "#Function<" <> contents = inspect(function)

    Algebra.concat([
      "#Function<",
      Algebra.nest(
        Algebra.concat([
          Algebra.line(),
          binary_slice(contents, 0..-2//1),
          Algebra.line(),
          to_algebra(ast, diff_wrapper)
        ]),
        2
      ),
      Algebra.line(),
      ">"
    ])
  end

  # Diff helpers

  defp add_hint(%{hints: hints} = env, hint) do
    if hint in hints, do: env, else: %{env | hints: [hint | hints]}
  end

  defp maybe_escape(other, %{context: :match}), do: other
  defp maybe_escape(other, _env), do: escape(other)

  # We escape container types to make a distinction between AST and values that
  # should be inspected. Maps and structs without custom inspect implementation
  # should not be inspected, convert it to ast.
  # All other values have no special AST representation, so we can keep them as is.
  defp escape(other) when is_map(other) do
    struct = maybe_struct(other)

    if struct && Inspect.impl_for(other) not in [Inspect.Any, Inspect.Map] do
      other
    else
      other
      |> Map.to_list()
      |> Enum.sort()
      |> Enum.map(&escape_pair/1)
      |> build_map_or_struct(struct)
    end
  end

  defp escape(other) when is_list(other) or is_tuple(other), do: {other}
  defp escape(other), do: other

  defp escape_pair({key, value}), do: {escape(key), escape(value)}

  defp merge_diff(%__MODULE__{} = result1, %__MODULE__{} = result2, fun) do
    {left, right} = fun.(result1.left, result2.left, result1.right, result2.right)

    %__MODULE__{
      equivalent?: result1.equivalent? && result2.equivalent?,
      left: left,
      right: right
    }
  end

  defp update_diff_meta({left, meta, right}, false) when is_list(meta),
    do: {left, Keyword.delete(meta, :diff), right}

  defp update_diff_meta({left, meta, right}, true) when is_list(meta),
    do: {left, Keyword.put(meta, :diff, true), right}

  defp update_diff_meta(literal, false),
    do: literal

  defp update_diff_meta(literal, true),
    do: {:__block__, [diff: true], [literal]}

  defp extract_diff_meta({:__block__, [diff: true], [literal]}),
    do: {literal, true}

  defp extract_diff_meta({left, meta, right}) when is_list(meta),
    do: {{left, meta, right}, !!meta[:diff]}

  defp extract_diff_meta(other), do: {other, false}

  defp keyword?(quoted) do
    {pair, _} = extract_diff_meta(quoted)
    safe_keyword?(pair)
  end

  defp safe_keyword?({key, _value}), do: key_is_atom?(key)
  defp safe_keyword?({:{}, _meta, [key, _value]}), do: key_is_atom?(key)
  defp safe_keyword?(_other), do: false

  defp key_is_atom?(quoted) do
    {key, _} = extract_diff_meta(quoted)
    is_atom(key)
  end

  defp var_context({name, meta, context}) do
    {name, meta[:counter] || context}
  end

  defp safe_eval(expr) do
    Code.eval_quoted(expr, [])
  rescue
    _ -> :error
  end

  defp safe_inspect(value) do
    {:ok, inspect(value, safe: false)}
  rescue
    _ -> :error
  end
end
