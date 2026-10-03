# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

Code.require_file("type_helper.exs", __DIR__)

defmodule Module.Types.TallyTest do
  use ExUnit.Case, async: false

  import Module.Types.Descr

  describe "bounds" do
    test "solves trivial, closed, and rigid constraints" do
      x = var(:x)
      y = var(:y)

      assert tally([]) == [%{}]
      assert tally([{integer(), term()}]) == [%{}]
      assert tally([{integer(), atom()}]) == []
      assert tally([{x, y}], [x, y]) == []
    end

    test "computes principal upper and lower bounds" do
      x = var(:x)
      rigid = var(:rigid)

      upper = tally([{x, rigid}], [rigid])
      lower = tally([{rigid, x}], [rigid])

      assert_solution(upper, %{x => opt_intersection(x, rigid)})
      assert_solution(lower, %{x => opt_union(x, rigid)})
      assert_sound(upper, [{x, rigid}])
      assert_sound(lower, [{rigid, x}])
    end

    test "keeps residual variables in principal solutions" do
      x = var(:x)
      y = var(:y)

      solutions = tally([{x, y}])

      assert_solution(solutions, %{x => opt_intersection(x, y)})
      assert MapSet.subset?(vars(Map.fetch!(hd(solutions), x)), MapSet.new([x, y]))
      assert_sound(solutions, [{x, y}])
    end

    test "merges and propagates bounds" do
      x = var(:x)
      number = opt_union(integer(), float())
      constraints = [{integer(), x}, {x, number}]

      solutions = tally(constraints)

      assert_solution(solutions, %{
        x => opt_intersection(opt_union(x, integer()), number)
      })

      assert_sound(solutions, constraints)

      a = var(:a)
      b = var(:b)
      assert tally([{a, b}, {b, integer()}, {atom(), a}]) == []
    end
  end

  describe "constructors" do
    test "uses function argument contravariance and result covariance" do
      x = var(:x)
      y = var(:y)
      argument = var(:argument)
      result = var(:result)
      constraints = [{fun([x], y), fun([argument], result)}]

      solutions = tally(constraints, [argument, result])

      assert_solution(solutions, %{
        x => opt_union(x, argument),
        y => opt_intersection(y, result)
      })

      assert_sound(solutions, constraints)
    end

    test "branches across tuple coordinates" do
      x = var(:x)
      y = var(:y)
      first = var(:first)
      second = var(:second)
      constraints = [{tuple([x, y]), tuple([first, second])}]

      solutions = tally(constraints, [first, second])

      assert length(solutions) == 3
      assert_solution(solutions, %{x => none()})
      assert_solution(solutions, %{y => none()})

      assert_solution(solutions, %{
        x => opt_intersection(x, first),
        y => opt_intersection(y, second)
      })

      assert_sound(solutions, constraints)
    end

    test "preserves homogeneous list alternatives" do
      x = var(:x)

      constraints = [
        {non_empty_list(x),
         opt_union(non_empty_list(atom([true])), non_empty_list(atom([false])))}
      ]

      solutions = tally(constraints)

      assert length(solutions) == 2
      assert_solution(solutions, %{x => opt_intersection(x, atom([true]))})
      assert_solution(solutions, %{x => opt_intersection(x, atom([false]))})
      assert_sound(solutions, constraints)
    end

    test "normalizes required and optional map fields" do
      x = var(:x)
      rigid = var(:rigid)

      required = [{closed_map(value: x), closed_map(value: rigid)}]
      optional = [{closed_map(value: if_set(x)), closed_map(value: if_set(rigid))}]

      required_solutions = tally(required, [rigid])
      optional_solutions = tally(optional, [rigid])

      assert_solution(required_solutions, %{x => opt_intersection(x, rigid)})
      assert_solution(optional_solutions, %{x => opt_intersection(x, rigid)})
      assert_sound(required_solutions, required)
      assert_sound(optional_solutions, optional)
    end
  end

  describe "recursive solving" do
    @tag timeout: 2_000
    test "ties contractive equations into recursive descriptors" do
      x = var(:x)
      constraints = [{x, tuple([x])}]

      assert [%{^x => solution}] = solutions = tally(constraints)
      assert match?({_, _, _}, solution)
      assert_sound(solutions, constraints)
    end
  end

  describe "validation" do
    test "rejects malformed, gradual, and non-variable inputs" do
      x = var(:x)

      assert_raise ArgumentError, ~r/constraint/, fn -> tally([integer()]) end
      assert_raise ArgumentError, ~r/static types/, fn -> tally([{dynamic(), x}]) end
      assert_raise ArgumentError, ~r/type variable/, fn -> tally([{x, term()}], [integer()]) end
      assert_raise ArgumentError, ~r/MapSet or list/, fn -> tally([{x, term()}], :fixed) end
    end
  end

  defp assert_solution(solutions, expected) do
    assert Enum.any?(solutions, fn solution ->
             map_size(solution) == map_size(expected) and
               Enum.all?(expected, fn {variable, expected_type} ->
                 case Map.fetch(solution, variable) do
                   {:ok, actual_type} -> equal?(actual_type, expected_type)
                   :error -> false
                 end
               end)
           end),
           "expected a semantically equivalent solution"
  end

  defp assert_sound(solutions, constraints) do
    assert solutions != []

    for solution <- solutions, {left, right} <- constraints do
      assert subtype?(substitute(left, solution), substitute(right, solution))
    end
  end
end
