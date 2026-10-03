# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

defmodule Module.Types.Descr.Tally do
  @moduledoc false

  # This is the three-stage tallying algorithm from Section 5.2 of
  # "Implementing Set-Theoretic Types":
  #
  #   1. normalize each `left \\ right` emptiness problem into incomparable
  #      normalized bound sets;
  #   2. propagate the subtyping obligations induced by those bounds;
  #   3. turn every saturated bound set into a principal substitution.
  #
  # The constraint-set machinery follows SSTT's type-variable implementation.
  # Constructor normalization mirrors the emptiness recurrences in Descr, with
  # Boolean conjunction/disjunction replaced by intersection/union of solution
  # families.

  alias Module.Types.Descr
  alias Module.Types.Descr.Polymorphic, as: Poly

  @domain_key_types :lists.sort(
                      [:binary, :bitstring_no_binary, :integer, :float, :pid, :port, :reference] ++
                        [:fun, :atom, :tuple, :map, :list]
                    )

  @type constraint :: {term(), term(), term()}
  @type constraint_set :: [constraint()]
  @type constraint_sets :: [constraint_set()]

  def tally(constraints, fixed) when is_list(constraints) do
    fixed = normalize_fixed(fixed)
    constraints = validate_constraints!(constraints)

    state = %{
      fixed: fixed,
      fixed_identities: MapSet.new(fixed, &variable_identity!/1),
      memo: :ets.new(:descr_tally_memo, [:set, :private])
    }

    try do
      normalized =
        Enum.reduce(constraints, css_any(), fn {left, right}, acc ->
          css_cap_lazy(acc, fn -> normalize(Descr.difference(left, right), state) end, state)
        end)

      propagated =
        Enum.reduce(normalized, css_empty(), fn constraint_set, acc ->
          css_cup(acc, propagate(constraint_set, state), state)
        end)

      propagated
      |> Enum.reduce([], fn constraint_set, acc ->
        case solve(constraint_set) do
          {:ok, substitution} ->
            if valid_solution?(substitution, constraints) do
              add_solution(substitution, acc)
            else
              acc
            end

          :non_contractive ->
            acc
        end
      end)
      |> Enum.reverse()
    after
      :ets.delete(state.memo)
    end
  end

  defp normalize_fixed(%MapSet{} = fixed), do: validate_fixed!(fixed)
  defp normalize_fixed(fixed) when is_list(fixed), do: fixed |> MapSet.new() |> validate_fixed!()

  defp normalize_fixed(other) do
    raise ArgumentError, "expected fixed variables to be a MapSet or list, got: #{inspect(other)}"
  end

  defp validate_fixed!(fixed) do
    Enum.each(fixed, &variable_identity!/1)
    fixed
  end

  defp validate_constraints!(constraints) do
    Enum.map(constraints, fn
      {left, right} ->
        if Descr.gradual?(left) or Descr.gradual?(right) do
          raise ArgumentError,
                "tallying is defined for static types, got: #{inspect({left, right})}"
        end

        {left, right}

      other ->
        raise ArgumentError,
              "expected a tallying constraint as a {left, right} pair, got: #{inspect(other)}"
    end)
  end

  ## Normalized constraints

  defp constraint(lower, variable, upper, state) do
    constraint = {lower, variable, upper}
    assert_satisfiable!([], constraint, state)
    constraint
  end

  defp constraint_variable({_lower, variable, _upper}), do: variable

  defp constraint_merge(
         {lower1, variable, upper1},
         {lower2, variable, upper2},
         state
       ) do
    constraint(
      Descr.union(lower1, lower2),
      variable,
      Descr.intersection(upper1, upper2),
      state
    )
  end

  defp constraint_subsumes?(
         context,
         {lower1, variable, upper1},
         {lower2, variable, upper2},
         _state
       ) do
    lower2 =
      Enum.reduce(context, lower2, fn {lower, context_variable, upper}, type ->
        bound(type, context_variable, lower, upper, :strengthen)
      end)

    upper2 =
      Enum.reduce(context, upper2, fn {lower, context_variable, upper}, type ->
        bound(type, context_variable, lower, upper, :weaken)
      end)

    Descr.subtype?(lower2, lower1) and Descr.subtype?(upper1, upper2)
  end

  defp assert_satisfiable!(context, {lower, _variable, upper}, state) do
    difference =
      Enum.reduce(context, Descr.difference(lower, upper), fn
        {context_lower, context_variable, context_upper}, type ->
          bound(type, context_variable, context_lower, context_upper, :weaken)
      end)

    if always_non_empty?(difference, state), do: throw(:tally_unsatisfiable)
  end

  defp always_non_empty?(type, state) do
    type =
      type
      |> Descr.top_vars()
      |> MapSet.difference(state.fixed)
      |> Enum.reduce(type, fn variable, type ->
        bound(type, variable_identity!(variable), Descr.term(), Descr.none(), :strengthen)
      end)

    MapSet.subset?(Descr.vars(type), state.fixed) and not Descr.empty?(type)
  end

  defp bound(type, variable, lower, upper, direction) do
    Descr.__tally_bound__(
      type,
      Descr.__tally_variable__(variable),
      lower,
      upper,
      direction
    )
  end

  ## Constraint sets

  defp cs_any(), do: []

  defp cs_add(constraint, [], _state), do: [constraint]

  defp cs_add(constraint, [head | tail] = constraints, state) do
    case compare_variables(constraint_variable(constraint), constraint_variable(head)) do
      :lt ->
        [constraint | constraints]

      :eq ->
        [constraint_merge(constraint, head, state) | tail]

      :gt ->
        tail = cs_add(constraint, tail, state)
        assert_satisfiable!(tail, head, state)
        [head | tail]
    end
  end

  defp cs_cap(left, right, state) do
    if length(right) <= length(left) do
      Enum.reduce(right, left, &cs_add(&1, &2, state))
    else
      Enum.reduce(left, right, &cs_add(&1, &2, state))
    end
  end

  defp cs_subsumes?(left, right, state) do
    cs_subsumes_reverse?(Enum.reverse(left), Enum.reverse(right), [], state)
  end

  defp cs_subsumes_reverse?(_left, [], _context, _state), do: true
  defp cs_subsumes_reverse?([], _right, _context, _state), do: false

  defp cs_subsumes_reverse?(
         [left | lefts] = all_left,
         [right | rights] = all_right,
         context,
         state
       ) do
    left_variable = constraint_variable(left)
    right_variable = constraint_variable(right)

    case compare_variables(left_variable, right_variable) do
      :gt ->
        cs_subsumes_reverse?(lefts, all_right, [left | context], state)

      :lt ->
        trivial = {Descr.none(), right_variable, Descr.term()}

        constraint_subsumes?(context, trivial, right, state) and
          cs_subsumes_reverse?(all_left, rights, context, state)

      :eq ->
        constraint_subsumes?(context, left, right, state) and
          cs_subsumes_reverse?(lefts, rights, [left | context], state)
    end
  end

  ## Sets of constraint sets

  defp css_empty(), do: []
  defp css_any(), do: [cs_any()]

  defp css_single_constraint(constraint, state) do
    try do
      [[constraint(elem(constraint, 0), elem(constraint, 1), elem(constraint, 2), state)]]
    catch
      :tally_unsatisfiable -> css_empty()
    end
  end

  defp css_add(constraint_set, constraint_sets, state) do
    if Enum.any?(constraint_sets, &cs_subsumes?(constraint_set, &1, state)) do
      constraint_sets
    else
      constraint_sets
      |> Enum.reject(&cs_subsumes?(&1, constraint_set, state))
      |> insert_ordered(constraint_set)
    end
  end

  defp css_cup(left, right, state), do: Enum.reduce(right, left, &css_add(&1, &2, state))

  defp css_cap(left, right, state) do
    for left_set <- left, right_set <- right, reduce: css_empty() do
      acc ->
        try do
          css_add(cs_cap(left_set, right_set, state), acc, state)
        catch
          :tally_unsatisfiable -> acc
        end
    end
  end

  defp css_cup_lazy(left, right, state) do
    if left == css_any(), do: left, else: css_cup(left, right.(), state)
  end

  defp css_cap_lazy(left, right, state) do
    if left == css_empty(), do: left, else: css_cap(left, right.(), state)
  end

  defp css_map_conj(enumerable, fun, state) do
    Enum.reduce_while(enumerable, css_any(), fn element, acc ->
      result = css_cap_lazy(acc, fn -> fun.(element) end, state)
      if result == css_empty(), do: {:halt, result}, else: {:cont, result}
    end)
  end

  defp css_map_disj(enumerable, fun, state) do
    Enum.reduce_while(enumerable, css_empty(), fn element, acc ->
      result = css_cup_lazy(acc, fn -> fun.(element) end, state)
      if result == css_any(), do: {:halt, result}, else: {:cont, result}
    end)
  end

  defp insert_ordered([], value), do: [value]

  defp insert_ordered([head | tail] = values, value) do
    cond do
      value < head -> [value | values]
      value == head -> values
      true -> [head | insert_ordered(tail, value)]
    end
  end

  ## Normalize

  defp normalize(type, state) do
    cond do
      Descr.empty?(type) ->
        css_any()

      MapSet.subset?(Descr.vars(type), state.fixed) ->
        css_empty()

      true ->
        normalize_type(type, state)
    end
  end

  defp normalize_type({:type_variables, bdd}, state) do
    bdd
    |> Poly.to_dnf()
    |> css_map_conj(&normalize_summand(&1, state), state)
  end

  defp normalize_type({id, _recursive_state, _generator} = node, state) do
    key = {:recursive, id}

    case :ets.lookup(state.memo, key) do
      [{^key, constraints}] ->
        constraints

      [] ->
        :ets.insert(state.memo, {key, css_any()})

        try do
          normalize_type(Descr.to_descr(node), state)
        after
          :ets.delete(state.memo, key)
        end
    end
  end

  defp normalize_type(:term, _state), do: css_empty()

  defp normalize_type(%{} = descr, state) do
    normalize_descr(descr, state)
  end

  defp normalize_summand({positive, negative, descr}, state) do
    candidates =
      (positive ++ negative)
      |> Enum.reject(&MapSet.member?(state.fixed_identities, &1))
      |> Enum.sort()

    case candidates do
      [variable | _] ->
        if variable in positive do
          rest = line_type(List.delete(positive, variable), negative, descr)
          css_single_constraint({Descr.none(), variable, Descr.negation(rest)}, state)
        else
          rest = line_type(positive, List.delete(negative, variable), descr)
          css_single_constraint({rest, variable, Descr.term()}, state)
        end

      [] ->
        normalize_descr(descr, state)
    end
  end

  defp line_type(positive, negative, descr) do
    type =
      Enum.reduce(positive, descr, fn variable, type ->
        Descr.intersection(Descr.__tally_variable__(variable), type)
      end)

    Enum.reduce(negative, type, fn variable, type ->
      Descr.difference(type, Descr.__tally_variable__(variable))
    end)
  end

  defp normalize_descr(descr, _state) when map_size(descr) == 0, do: css_any()

  defp normalize_descr(descr, state) do
    css_map_conj(
      descr,
      fn
        {:tuple, bdd} -> normalize_tuple(bdd, state)
        {:map, bdd} -> normalize_map(bdd, state)
        {:list, bdd} -> normalize_list(bdd, state)
        {:fun, functions} -> normalize_fun(functions, state)
        {:dynamic, _type} -> css_empty()
        {_constant_component, _value} -> css_empty()
      end,
      state
    )
  end

  ## Function normalization

  defp normalize_fun({:negation, _functions}, _state), do: css_empty()

  defp normalize_fun({:union, functions}, state) do
    css_map_conj(
      functions,
      fn {_arity, bdd} ->
        bdd
        |> Descr.bdd_to_dnf()
        |> css_map_conj(&normalize_arrow_line(&1, state), state)
      end,
      state
    )
  end

  defp normalize_arrow_line({positives, negatives}, state) do
    css_map_disj(negatives, &normalize_negative_arrow(positives, &1, state), state)
  end

  defp normalize_negative_arrow(positives, negative, state) do
    {negative_arguments, negative_return} = arrow_literal(negative)
    negative_domain = Descr.args_to_domain(negative_arguments)

    positive_domain =
      Enum.reduce(positives, Descr.none(), fn positive, acc ->
        {arguments, _return} = arrow_literal(positive)
        Descr.union(acc, Descr.args_to_domain(arguments))
      end)

    domain_constraints = normalize(Descr.difference(negative_domain, positive_domain), state)

    css_cap_lazy(
      domain_constraints,
      fn ->
        case positives do
          [] ->
            css_any()

          [_ | _] ->
            normalize_arrow_psi(
              negative_domain,
              Descr.negation(negative_return),
              positives,
              state
            )
        end
      end,
      state
    )
  end

  defp normalize_arrow_psi(domain, return, positives, state) do
    constraints = css_cup(normalize(domain, state), normalize(return, state), state)

    case positives do
      [] ->
        constraints

      [positive | rest] ->
        {arguments, positive_return} = arrow_literal(positive)
        positive_domain = Descr.args_to_domain(arguments)

        recursive =
          if Descr.disjoint?(domain, positive_domain) or Descr.subtype?(return, positive_return) do
            normalize_arrow_psi(domain, return, rest, state)
          else
            left =
              normalize_arrow_psi(Descr.difference(domain, positive_domain), return, rest, state)

            css_cap_lazy(
              left,
              fn ->
                normalize_arrow_psi(
                  domain,
                  Descr.intersection(return, positive_return),
                  rest,
                  state
                )
              end,
              state
            )
          end

        css_cup(constraints, recursive, state)
    end
  end

  defp arrow_literal({_hash, arguments, return}), do: {arguments, return}

  ## List normalization

  defp normalize_list(bdd, state) do
    bdd
    |> Descr.bdd_to_dnf()
    |> css_map_conj(
      fn {positives, negatives} ->
        {head, tail} =
          Enum.reduce(positives, {Descr.term(), Descr.term()}, fn
            {_hash, next_head, next_tail}, {head, tail} ->
              {Descr.intersection(head, next_head), Descr.intersection(tail, next_tail)}
          end)

        tail = Descr.__tally_list_tail__(tail)

        negatives =
          Enum.map(negatives, fn {_hash, negative_head, negative_tail} ->
            {negative_head, Descr.__tally_list_tail__(negative_tail)}
          end)

        normalize_list_line(head, tail, negatives, state)
      end,
      state
    )
  end

  defp normalize_list_line(head, tail, [], state) do
    css_cup(normalize(head, state), normalize(tail, state), state)
  end

  defp normalize_list_line(head, tail, [{negative_head, negative_tail} | negatives], state) do
    skipped = normalize_list_line(head, tail, negatives, state)

    covered =
      normalize(Descr.difference(head, negative_head), state)
      |> css_cap_lazy(
        fn ->
          normalize_list_line(
            head,
            Descr.difference(tail, negative_tail),
            negatives,
            state
          )
        end,
        state
      )

    css_cup(skipped, covered, state)
  end

  ## Tuple normalization

  defp normalize_tuple(bdd, state) do
    bdd
    |> Descr.bdd_to_dnf()
    |> css_map_conj(
      fn {positives, negatives} ->
        case Descr.__tally_tuple_intersection__(positives) do
          :empty -> css_any()
          {tag, elements} -> normalize_tuple_line(tag, elements, negatives, state)
        end
      end,
      state
    )
  end

  defp normalize_tuple_line(_tag, elements, [], state) do
    css_map_disj(elements, &normalize(&1, state), state)
  end

  defp normalize_tuple_line(_tag, _elements, [{_hash, :open, []} | _rest], _state),
    do: css_any()

  defp normalize_tuple_line(:open, elements, [{_hash, :closed, _negative_elements}], state) do
    css_map_disj(elements, &normalize(&1, state), state)
  end

  defp normalize_tuple_line(
         tag,
         elements,
         [{_hash, negative_tag, negative_elements} | negatives],
         state
       ) do
    n = length(elements)
    m = length(negative_elements)

    if (tag == :closed and n < m) or (negative_tag == :closed and n > m) do
      normalize_tuple_line(tag, elements, negatives, state)
    else
      normalize_tuple_elements([], tag, elements, negative_elements, negatives, state)
      |> css_cap(
        normalize_tuple_arity(n, m, tag, elements, negative_tag, negatives, state),
        state
      )
    end
  end

  defp normalize_tuple_elements(_meet, _tag, _elements, [], _negatives, _state),
    do: css_any()

  defp normalize_tuple_elements(
         meet,
         tag,
         elements,
         [negative | negative_elements],
         negatives,
         state
       ) do
    {type, elements} =
      case elements do
        [type | elements] -> {type, elements}
        [] -> {Descr.term(), []}
      end

    difference = Descr.difference(type, negative)
    intersection = Descr.intersection(type, negative)

    difference_branch =
      css_cup_lazy(
        normalize(difference, state),
        fn ->
          normalize_tuple_line(
            tag,
            Enum.reverse(meet, [difference | elements]),
            negatives,
            state
          )
        end,
        state
      )

    intersection_branch =
      css_cup_lazy(
        normalize(intersection, state),
        fn ->
          normalize_tuple_elements(
            [intersection | meet],
            tag,
            elements,
            negative_elements,
            negatives,
            state
          )
        end,
        state
      )

    css_cap(difference_branch, intersection_branch, state)
  end

  defp normalize_tuple_arity(_n, _m, :closed, _elements, _negative_tag, _negatives, _state),
    do: css_any()

  defp normalize_tuple_arity(n, m, :open, elements, negative_tag, negatives, state) do
    sizes = if n < m, do: Enum.to_list(n..(m - 1)), else: []

    constraints =
      css_map_conj(
        sizes,
        fn size ->
          normalize_tuple_line(:closed, tuple_fill(elements, size), negatives, state)
        end,
        state
      )

    if negative_tag == :open do
      constraints
    else
      css_cap_lazy(
        constraints,
        fn ->
          normalize_tuple_line(:open, tuple_fill(elements, m + 1), negatives, state)
        end,
        state
      )
    end
  end

  defp tuple_fill(elements, size) do
    elements ++ List.duplicate(Descr.term(), max(size - length(elements), 0))
  end

  ## Map normalization

  defp normalize_map(bdd, state) do
    bdd
    |> Descr.bdd_to_dnf()
    |> css_map_conj(
      fn {positives, negatives} ->
        case Descr.__tally_map_intersection__(positives) do
          :empty ->
            css_any()

          {tag, fields} ->
            fields_constraints =
              css_map_disj(fields, fn {_key, type} -> normalize(type, state) end, state)

            css_cup(fields_constraints, normalize_map_line(tag, fields, negatives, state), state)
        end
      end,
      state
    )
  end

  defp normalize_map_line(_tag, _fields, [], _state), do: css_empty()

  defp normalize_map_line(_tag, _fields, [{_hash, :open, []} | _rest], _state),
    do: css_any()

  defp normalize_map_line(:open, fields, [{_hash, :closed, _negative_fields} | negatives], state),
    do: normalize_map_line(:open, fields, negatives, state)

  defp normalize_map_line(
         tag,
         fields,
         [{_hash, negative_tag, negative_fields} | negatives],
         state
       ) do
    skipped = normalize_map_line(tag, fields, negatives, state)
    domain_constraints = normalize_map_domains(tag, negative_tag, state)

    used =
      css_cap_lazy(
        domain_constraints,
        fn ->
          if tag == :closed or negative_tag == :open do
            normalize_map_meet(fields, negative_fields, tag, negative_tag, [], negatives, state)
          else
            normalize_map_fields(
              fields,
              negative_fields,
              tag,
              negative_tag,
              fields,
              negatives,
              state
            )
          end
        end,
        state
      )

    css_cup(skipped, used, state)
  end

  defp normalize_map_domains(:closed, _negative_tag, _state), do: css_any()
  defp normalize_map_domains(_tag, :open, _state), do: css_any()

  defp normalize_map_domains(:open, negative_domains, state) when is_list(negative_domains) do
    if length(negative_domains) == length(@domain_key_types) do
      css_map_conj(
        negative_domains,
        fn {_domain_key, type} ->
          normalize(Descr.difference(term_or_optional(), type), state)
        end,
        state
      )
    else
      css_empty()
    end
  end

  defp normalize_map_domains(domains, :closed, state) when is_list(domains) do
    css_map_conj(
      domains,
      fn {_domain_key, type} ->
        normalize(Descr.__tally_remove_optional__(type), state)
      end,
      state
    )
  end

  defp normalize_map_domains(domains, negative_domains, state)
       when is_list(domains) and is_list(negative_domains) do
    css_map_conj(
      domains,
      fn {domain_key, type} ->
        negative = field_get(negative_domains, domain_key, Descr.not_set())
        normalize(Descr.difference(type, negative), state)
      end,
      state
    )
  end

  defp normalize_map_meet([], [], _tag, _negative_tag, _meet, _negatives, _state),
    do: css_any()

  defp normalize_map_meet(
         [{key1, type1} | fields1] = all_fields1,
         [{key2, type2} | fields2] = all_fields2,
         tag,
         negative_tag,
         meet,
         negatives,
         state
       ) do
    cond do
      key1 < key2 ->
        cond do
          negative_tag == :open ->
            normalize_map_meet(
              fields1,
              all_fields2,
              tag,
              negative_tag,
              [{key1, type1} | meet],
              negatives,
              state
            )

          negative_tag == :closed and not optional_static?(type1) ->
            css_empty()

          true ->
            normalize_map_meet_field(
              key1,
              type1,
              map_default(negative_tag),
              fields1,
              all_fields2,
              tag,
              negative_tag,
              meet,
              negatives,
              state
            )
        end

      key1 > key2 ->
        if tag == :closed and not optional_static?(type2) do
          css_empty()
        else
          normalize_map_meet_field(
            key2,
            map_default(tag),
            type2,
            all_fields1,
            fields2,
            tag,
            negative_tag,
            meet,
            negatives,
            state
          )
        end

      true ->
        normalize_map_meet_field(
          key1,
          type1,
          type2,
          fields1,
          fields2,
          tag,
          negative_tag,
          meet,
          negatives,
          state
        )
    end
  end

  defp normalize_map_meet([{key, type} | fields], [], tag, negative_tag, meet, negatives, state) do
    normalize_map_meet_field(
      key,
      type,
      map_default(negative_tag),
      fields,
      [],
      tag,
      negative_tag,
      meet,
      negatives,
      state
    )
  end

  defp normalize_map_meet([], [{key, type} | fields], tag, negative_tag, meet, negatives, state) do
    normalize_map_meet_field(
      key,
      map_default(tag),
      type,
      [],
      fields,
      tag,
      negative_tag,
      meet,
      negatives,
      state
    )
  end

  defp normalize_map_meet_field(
         key,
         type,
         negative_type,
         fields,
         negative_fields,
         tag,
         negative_tag,
         meet,
         negatives,
         state
       ) do
    difference = Descr.difference(type, negative_type)
    intersection = Descr.intersection(type, negative_type)

    difference_branch =
      css_cup_lazy(
        normalize(difference, state),
        fn ->
          normalize_map_line(
            tag,
            Enum.reverse(meet, [{key, difference} | fields]),
            negatives,
            state
          )
        end,
        state
      )

    intersection_branch =
      css_cup_lazy(
        normalize(intersection, state),
        fn ->
          normalize_map_meet(
            fields,
            negative_fields,
            tag,
            negative_tag,
            [{key, intersection} | meet],
            negatives,
            state
          )
        end,
        state
      )

    css_cap(difference_branch, intersection_branch, state)
  end

  defp normalize_map_fields([], [], _tag, _negative_tag, _fields, _negatives, _state),
    do: css_any()

  defp normalize_map_fields(
         [{key1, type1} | fields1] = all_fields1,
         [{key2, type2} | fields2] = all_fields2,
         tag,
         negative_tag,
         fields,
         negatives,
         state
       ) do
    cond do
      key1 < key2 ->
        cond do
          negative_tag == :open ->
            normalize_map_fields(
              fields1,
              all_fields2,
              tag,
              negative_tag,
              fields,
              negatives,
              state
            )

          negative_tag == :closed and not optional_static?(type1) ->
            css_empty()

          true ->
            normalize_map_field(
              key1,
              type1,
              map_default(negative_tag),
              tag,
              fields,
              negatives,
              state
            )
            |> css_cap(
              normalize_map_fields(
                fields1,
                all_fields2,
                tag,
                negative_tag,
                fields,
                negatives,
                state
              ),
              state
            )
        end

      key1 > key2 ->
        cond do
          tag == :closed and optional_static?(type2) ->
            normalize_map_fields(
              all_fields1,
              fields2,
              tag,
              negative_tag,
              fields,
              negatives,
              state
            )

          tag == :closed ->
            css_empty()

          true ->
            normalize_map_field(
              key2,
              map_default(tag),
              type2,
              tag,
              fields,
              negatives,
              state
            )
            |> css_cap(
              normalize_map_fields(
                all_fields1,
                fields2,
                tag,
                negative_tag,
                fields,
                negatives,
                state
              ),
              state
            )
        end

      true ->
        normalize_map_field(key1, type1, type2, tag, fields, negatives, state)
        |> css_cap(
          normalize_map_fields(
            fields1,
            fields2,
            tag,
            negative_tag,
            fields,
            negatives,
            state
          ),
          state
        )
    end
  end

  defp normalize_map_fields(fields1, fields2, tag, negative_tag, fields, negatives, state) do
    left =
      css_map_conj(
        fields1,
        fn {key, type} ->
          normalize_map_field(key, type, map_default(negative_tag), tag, fields, negatives, state)
        end,
        state
      )

    css_cap_lazy(
      left,
      fn ->
        css_map_conj(
          fields2,
          fn {key, type} ->
            normalize_map_field(key, map_default(tag), type, tag, fields, negatives, state)
          end,
          state
        )
      end,
      state
    )
  end

  defp normalize_map_field(key, type, negative_type, tag, fields, negatives, state) do
    difference = Descr.difference(type, negative_type)

    css_cup_lazy(
      normalize(difference, state),
      fn ->
        normalize_map_line(tag, :orddict.store(key, difference, fields), negatives, state)
      end,
      state
    )
  end

  defp map_default(:open), do: term_or_optional()
  defp map_default(:closed), do: Descr.not_set()
  defp map_default(domains) when is_list(domains), do: field_get(domains, :atom, Descr.not_set())

  defp term_or_optional(), do: Descr.if_set(Descr.term())
  defp optional_static?(type), do: Descr.subtype?(Descr.not_set(), type)

  defp field_get(fields, key, default) do
    case :orddict.find(key, fields) do
      {:ok, value} -> value
      :error -> default
    end
  end

  ## Propagate

  defp propagate(constraint_set, state) do
    propagate(cs_any(), constraint_set, MapSet.new(), state)
  end

  defp propagate(previous, [], _seen, _state), do: [previous]

  defp propagate(previous, [constraint | rest] = current, seen, state) do
    {lower, _variable, upper} = constraint
    induced = Descr.difference(lower, upper)

    if MapSet.member?(seen, induced) do
      try do
        propagate(cs_add(constraint, previous, state), rest, seen, state)
      catch
        :tally_unsatisfiable -> css_empty()
      end
    else
      combined =
        try do
          [cs_cap(previous, current, state)]
        catch
          :tally_unsatisfiable -> css_empty()
        end

      combined
      |> css_cap(normalize(induced, state), state)
      |> Enum.reduce(css_empty(), fn constraints, acc ->
        css_cup(acc, propagate(cs_any(), constraints, MapSet.put(seen, induced), state), state)
      end)
    end
  end

  ## Solve

  defp solve(constraint_set) do
    {equations, renaming} =
      Enum.map_reduce(constraint_set, %{}, fn {lower, variable, upper}, renaming ->
        original = Descr.__tally_variable__(variable)
        fresh = Descr.var(variable_name(variable))

        equation =
          lower
          |> Descr.union(fresh)
          |> Descr.intersection(upper)

        {{original, equation}, Map.put(renaming, fresh, original)}
      end)

    with {:ok, substitution} <- solve_equations(equations) do
      substitution =
        Map.new(substitution, fn {variable, type} ->
          {variable, Descr.substitute(type, renaming)}
        end)
        |> Enum.reject(&identity_substitution?/1)
        |> Map.new()

      {:ok, substitution}
    end
  end

  defp solve_equations([]), do: {:ok, %{}}

  defp solve_equations([{variable, equation} | equations]) do
    with {:ok, type} <- solve_recursive_equation(variable, equation),
         substitution = %{variable => type},
         equations =
           Enum.map(equations, fn {next_variable, next_equation} ->
             {next_variable, Descr.__tally_substitute__(next_equation, substitution)}
           end),
         {:ok, rest} <- solve_equations(equations) do
      {:ok, Map.put(rest, variable, Descr.__tally_substitute__(type, rest))}
    end
  end

  defp solve_recursive_equation(variable, equation) do
    cond do
      not MapSet.member?(Descr.vars(equation), variable) ->
        {:ok, equation}

      MapSet.member?(Descr.top_vars(equation), variable) ->
        :non_contractive

      true ->
        nodes =
          Descr.recursive(%{
            solution: fn recur ->
              Descr.__tally_substitute__(equation, %{variable => recur.(:solution)})
            end
          })

        {:ok, Map.fetch!(nodes, :solution)}
    end
  end

  defp valid_solution?(substitution, constraints) do
    Enum.all?(constraints, fn {left, right} ->
      left = Descr.__tally_substitute__(left, substitution)
      right = Descr.__tally_substitute__(right, substitution)
      Descr.subtype?(left, right)
    end)
  end

  defp identity_substitution?({_variable, {_, _, _}}), do: false
  defp identity_substitution?({variable, type}), do: Descr.equal?(variable, type)

  defp add_solution(substitution, solutions) do
    if Enum.any?(solutions, &equivalent_substitution?(&1, substitution)) do
      solutions
    else
      [substitution | solutions]
    end
  end

  defp equivalent_substitution?(left, right) when map_size(left) != map_size(right), do: false

  defp equivalent_substitution?(left, right) do
    Enum.all?(left, fn {variable, type} ->
      case Map.fetch(right, variable) do
        {:ok, other} -> equivalent_type?(type, other)
        :error -> false
      end
    end)
  end

  defp equivalent_type?({_, _, _} = left, {_, _, _} = right), do: left === right
  defp equivalent_type?({_, _, _}, _right), do: false
  defp equivalent_type?(_left, {_, _, _}), do: false
  defp equivalent_type?(left, right), do: Descr.equal?(left, right)

  ## Variables and ordering

  defp variable_identity!(variable) do
    case Descr.__tally_variable_identity__(variable) do
      {:ok, identity} -> identity
      :error -> raise ArgumentError, "expected a type variable, got: #{inspect(variable)}"
    end
  end

  defp variable_name({:type_variable, _id, name}), do: name

  defp compare_variables(left, right) do
    cond do
      left < right -> :lt
      left > right -> :gt
      true -> :eq
    end
  end
end
