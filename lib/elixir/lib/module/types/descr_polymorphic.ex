# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

defmodule Module.Types.Descr.Polymorphic do
  @moduledoc false

  # This is the outer decision diagram described in "Implementing
  # Set-Theoretic Types", Section 4.5. Its atoms are type variables and its
  # leaves are complete monomorphic descriptors.

  def leaf(descr), do: {:leaf, descr}

  def variable(variable, top, bottom) do
    node(variable, leaf(top), leaf(bottom))
  end

  def node(_variable, same, same), do: same
  def node(variable, positive, negative), do: {:node, variable, positive, negative}

  def union(left, right, leaf_union), do: operation(left, right, leaf_union)
  def intersection(left, right, leaf_intersection), do: operation(left, right, leaf_intersection)
  def difference(left, right, leaf_difference), do: operation(left, right, leaf_difference)

  def negation({:leaf, descr}, leaf_negation), do: leaf(leaf_negation.(descr))

  def negation({:node, variable, positive, negative}, leaf_negation) do
    node(
      variable,
      negation(positive, leaf_negation),
      negation(negative, leaf_negation)
    )
  end

  def map_leaves({:leaf, descr}, fun), do: leaf(fun.(descr))

  def map_leaves({:node, variable, positive, negative}, fun) do
    node(variable, map_leaves(positive, fun), map_leaves(negative, fun))
  end

  def all_leaves?(bdd, fun), do: reduce_leaves(bdd, true, &(&2 and fun.(&1)))

  def all_pairs?(left, right, fun), do: all_pairs(left, right, fun)

  def reduce_leaves({:leaf, descr}, acc, fun), do: fun.(descr, acc)

  def reduce_leaves({:node, _variable, positive, negative}, acc, fun) do
    acc = reduce_leaves(positive, acc, fun)
    reduce_leaves(negative, acc, fun)
  end

  def variables(bdd), do: variables(bdd, MapSet.new())

  defp variables({:leaf, _descr}, acc), do: acc

  defp variables({:node, variable, positive, negative}, acc) do
    acc = MapSet.put(acc, variable)
    acc = variables(positive, acc)
    variables(negative, acc)
  end

  defp all_pairs({:leaf, left}, {:leaf, right}, fun), do: fun.(left, right)

  defp all_pairs({:node, _variable, positive, negative}, {:leaf, _} = right, fun) do
    all_pairs(positive, right, fun) and all_pairs(negative, right, fun)
  end

  defp all_pairs({:leaf, _} = left, {:node, _variable, positive, negative}, fun) do
    all_pairs(left, positive, fun) and all_pairs(left, negative, fun)
  end

  defp all_pairs(
         {:node, left_variable, left_positive, left_negative} = left,
         {:node, right_variable, right_positive, right_negative} = right,
         fun
       ) do
    cond do
      left_variable < right_variable ->
        all_pairs(left_positive, right, fun) and all_pairs(left_negative, right, fun)

      left_variable > right_variable ->
        all_pairs(left, right_positive, fun) and all_pairs(left, right_negative, fun)

      true ->
        all_pairs(left_positive, right_positive, fun) and
          all_pairs(left_negative, right_negative, fun)
    end
  end

  def to_dnf(bdd), do: to_dnf(bdd, [], [], [])

  defp to_dnf({:leaf, descr}, positive, negative, acc) do
    [{Enum.reverse(positive), Enum.reverse(negative), descr} | acc]
  end

  defp to_dnf({:node, variable, positive, negative}, positives, negatives, acc) do
    acc = to_dnf(positive, [variable | positives], negatives, acc)
    to_dnf(negative, positives, [variable | negatives], acc)
  end

  def substitute(
        {:leaf, descr},
        substitutions,
        leaf_substitute,
        _lift,
        _leaf_union,
        _leaf_intersection,
        _leaf_difference
      ) do
    leaf(leaf_substitute.(descr, substitutions))
  end

  def substitute(
        {:node, variable, positive, negative},
        substitutions,
        leaf_substitute,
        lift,
        leaf_union,
        leaf_intersection,
        leaf_difference
      ) do
    positive =
      substitute(
        positive,
        substitutions,
        leaf_substitute,
        lift,
        leaf_union,
        leaf_intersection,
        leaf_difference
      )

    negative =
      substitute(
        negative,
        substitutions,
        leaf_substitute,
        lift,
        leaf_union,
        leaf_intersection,
        leaf_difference
      )

    replacement =
      case Map.fetch(substitutions, variable) do
        {:ok, descr} -> lift.(descr)
        :error -> node(variable, leaf(:term), leaf(%{}))
      end

    positive = intersection(replacement, positive, leaf_intersection)
    negative = difference(negative, replacement, leaf_difference)
    union(positive, negative, leaf_union)
  end

  # Replaces positive and negative occurrences of one variable independently.
  # Tallying uses this to refine a type under a bound `lower <= variable <= upper`:
  # strengthening maps positive occurrences to `variable and upper` and negative
  # occurrences to `variable or lower`; weakening performs the dual operation.
  #
  # Every Shannon node is rebuilt through the Boolean operations because either
  # replacement may introduce variables that precede the current node.
  def substitute_polarity(
        bdd,
        target,
        positive_replacement,
        negative_replacement,
        lift,
        leaf_union,
        leaf_intersection,
        leaf_difference
      ) do
    do_substitute_polarity(
      bdd,
      target,
      positive_replacement,
      negative_replacement,
      lift,
      leaf_union,
      leaf_intersection,
      leaf_difference
    )
  end

  defp do_substitute_polarity(
         {:leaf, _descr} = leaf,
         _target,
         _positive_replacement,
         _negative_replacement,
         _lift,
         _leaf_union,
         _leaf_intersection,
         _leaf_difference
       ),
       do: leaf

  defp do_substitute_polarity(
         {:node, variable, positive, negative},
         target,
         positive_replacement,
         negative_replacement,
         lift,
         leaf_union,
         leaf_intersection,
         leaf_difference
       ) do
    positive =
      do_substitute_polarity(
        positive,
        target,
        positive_replacement,
        negative_replacement,
        lift,
        leaf_union,
        leaf_intersection,
        leaf_difference
      )

    negative =
      do_substitute_polarity(
        negative,
        target,
        positive_replacement,
        negative_replacement,
        lift,
        leaf_union,
        leaf_intersection,
        leaf_difference
      )

    {positive_literal, negative_literal} =
      if variable == target do
        {lift.(positive_replacement), lift.(negative_replacement)}
      else
        literal = variable(variable, :term, %{})
        {literal, literal}
      end

    positive = intersection(positive_literal, positive, leaf_intersection)
    negative = difference(negative, negative_literal, leaf_difference)
    union(positive, negative, leaf_union)
  end

  defp operation({:leaf, left}, {:leaf, right}, leaf_operation) do
    leaf(leaf_operation.(left, right))
  end

  defp operation({:node, variable, positive, negative}, {:leaf, _} = right, leaf_operation) do
    node(
      variable,
      operation(positive, right, leaf_operation),
      operation(negative, right, leaf_operation)
    )
  end

  defp operation({:leaf, _} = left, {:node, variable, positive, negative}, leaf_operation) do
    node(
      variable,
      operation(left, positive, leaf_operation),
      operation(left, negative, leaf_operation)
    )
  end

  defp operation(
         {:node, left_variable, left_positive, left_negative} = left,
         {:node, right_variable, right_positive, right_negative} = right,
         leaf_operation
       ) do
    cond do
      left_variable < right_variable ->
        node(
          left_variable,
          operation(left_positive, right, leaf_operation),
          operation(left_negative, right, leaf_operation)
        )

      left_variable > right_variable ->
        node(
          right_variable,
          operation(left, right_positive, leaf_operation),
          operation(left, right_negative, leaf_operation)
        )

      true ->
        node(
          left_variable,
          operation(left_positive, right_positive, leaf_operation),
          operation(left_negative, right_negative, leaf_operation)
        )
    end
  end
end
