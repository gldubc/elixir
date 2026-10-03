# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

Code.require_file("type_helper.exs", __DIR__)

defmodule Module.Types.TypeVariablesTest do
  use ExUnit.Case, async: true

  import Module.Types.Descr

  describe "identity and Boolean operations" do
    test "variables with the same display name have fresh identities" do
      x1 = var(:x)
      x2 = var(:x)

      refute equal?(x1, x2)
      refute subtype?(x1, x2)
      refute subtype?(x2, x1)
      assert to_quoted_string(x1) == "x"
      assert to_quoted_string(x2) == "x"
    end

    test "implements the variable laws from SSTT" do
      x = var(:x)
      y = var(:y)
      z = var(:z)

      assert subtype?(opt_intersection(x, y), x)
      refute subtype?(opt_intersection(z, y), x)
      assert empty?(opt_intersection(x, opt_negation(x)))
      assert equal?(opt_union(x, opt_negation(x)), term())

      assert opt_union(opt_intersection(x, integer()), opt_difference(x, integer()))
             |> equal?(x)
    end

    test "uses universal-substitution subtyping" do
      x = var(:x)
      y = var(:y)

      refute empty?(x)
      refute empty?(opt_negation(x))
      refute empty?(opt_intersection(x, y))
      refute empty?(opt_difference(x, y))

      assert subtype?(none(), x)
      assert subtype?(x, term())
      refute subtype?(x, integer())
      refute subtype?(integer(), x)
      assert subtype?(opt_intersection(x, integer()), integer())
      refute disjoint?(x, integer())
      assert disjoint?(x, opt_negation(x))
    end

    test "keeps bare and optimized operations equivalent" do
      x = var(:x)
      y = var(:y)

      pairs = [
        {bare_union(x, y), opt_union(x, y)},
        {bare_intersection(x, integer()), opt_intersection(x, integer())},
        {bare_difference(x, y), opt_difference(x, y)},
        {bare_negation(opt_union(x, integer())), opt_negation(opt_union(x, integer()))}
      ]

      for {bare, optimized} <- pairs do
        assert equal?(bare, optimized)
      end
    end
  end

  describe "constructors" do
    test "supports variables below tuples, lists, maps, and functions" do
      x = var(:x)
      not_x = opt_negation(x)

      assert empty?(opt_intersection(tuple([x]), tuple([not_x])))

      assert empty?(
               opt_intersection(
                 non_empty_list(x, empty_list()),
                 non_empty_list(not_x, empty_list())
               )
             )

      assert empty?(opt_intersection(closed_map(a: x), closed_map(a: not_x)))

      assert subtype?(fun([term()], x), fun([term()], term()))
      refute subtype?(fun([term()], term()), fun([term()], x))
      assert subtype?(fun([term()], term()), fun([x], term()))
      refute subtype?(fun([x], term()), fun([term()], term()))
    end

    test "supports variables in improper-list tails" do
      x = var(:x)
      type = non_empty_list(integer(), x)

      assert vars(type) == MapSet.new([x])
      assert substitute(type, %{x => atom()}) |> equal?(non_empty_list(integer(), atom()))
    end

    test "recognizes polymorphic optional map fields" do
      x = var(:x)
      map = closed_map(value: if_set(x))

      assert subtype?(empty_map(), map)

      for intersection <- [opt_intersection(empty_map(), map), opt_intersection(map, empty_map())] do
        refute empty?(intersection)
        assert equal?(intersection, empty_map())
      end
    end

    test "projects top-level variables for constructor-specific operations" do
      x = var(:x)

      assert booleaness(x) == :maybe_both
      assert truthiness(x) == :undefined
      assert atom_fetch(x) == :error
      assert fun_apply(x, [integer()]) == :badfun
      assert list_hd(x) == :badnonemptylist
      assert map_fetch_key(x, :value) == :badmap
      assert map_put(x, atom([:value]), integer()) == :badmap
      assert map_put_key(x, :value, integer()) == :badmap
      assert map_update(x, atom([:value]), integer()) == :badmap
      assert map_update_fun(x, atom([:value]), fn _ -> integer() end) == :badmap

      assert map_update_unchecked(x, atom([:value]), fn _, _ -> integer() end, true, false) ==
               :badmap

      assert tuple_fetch(x, 0) == :badtuple
      assert tuple_delete_at(x, 0) == :badtuple
      assert tuple_insert_at(x, 0, integer()) == :badtuple
      assert tuple_replace_at(x, 0, integer()) == :badtuple

      assert {:finite, [:ok]} = atom_fetch(opt_intersection(x, atom([:ok])))
      assert {:ok, output} = fun_apply(opt_intersection(x, fun([integer()], atom())), [integer()])
      assert equal?(output, atom())
      assert {:ok, head} = list_hd(opt_intersection(x, non_empty_list(integer())))
      assert equal?(head, integer())

      assert {false, value} =
               map_fetch_key(opt_intersection(x, closed_map(value: integer())), :value)

      assert equal?(value, integer())
      assert {false, element} = tuple_fetch(opt_intersection(x, tuple([integer()])), 0)
      assert equal?(element, integer())

      assert {:ok, map_with_x} = map_put_key(empty_map(), :value, x)
      assert {false, map_value} = map_fetch_key(map_with_x, :value)
      assert equal?(map_value, x)

      tuple_with_x = tuple_insert_at(tuple([integer()]), 1, x)
      assert {false, tuple_value} = tuple_fetch(tuple_with_x, 1)
      assert equal?(tuple_value, x)
    end

    test "tracks top-level and nested meaningful variables" do
      x = var(:x)
      y = var(:y)
      type = tuple([x, closed_map(value: y)])

      assert top_vars(x) == MapSet.new([x])
      assert top_vars(type) == MapSet.new()
      assert vars(type) == MapSet.new([x, y])

      assert vars(opt_union(x, opt_negation(x))) == MapSet.new()
      assert vars(opt_intersection(x, none())) == MapSet.new()
      assert vars(opt_intersection(x, integer())) == MapSet.new([x])
    end

    test "maps gradual bounds over variables" do
      x = var(:x)
      dynamic_x = dynamic(x)

      assert gradual?(dynamic_x)
      assert subtype?(dynamic_x, dynamic_x)
      assert subtype?(dynamic_x, dynamic())
      assert equal?(dynamic_x, dynamic_x)
      refute disjoint?(dynamic_x, dynamic_x)
      x_integer = opt_intersection(x, integer())
      assert compatible?(x_integer, integer())
      assert {:ok, compatible} = compatible_intersection(x_integer, integer())
      assert equal?(compatible, opt_union(dynamic(x_integer), x_integer))
      assert equal?(upper_bound(dynamic_x), x)
      assert empty?(lower_bound(dynamic_x))
      assert vars(dynamic_x) == MapSet.new([x])
    end
  end

  describe "substitution" do
    test "is simultaneous and preserves unmapped variables" do
      x = var(:x)
      y = var(:y)
      type = tuple([x, y])

      substituted = substitute(type, %{x => y, y => integer()})

      assert equal?(substituted, tuple([y, integer()]))
      assert vars(substituted) == MapSet.new([y])
      assert vars(type) == MapSet.new([x, y])
      assert equal?(substitute(x, %{x => tuple([x])}), tuple([x]))
    end

    test "respects positive and negative occurrences" do
      x = var(:x)
      type = opt_union(x, opt_negation(tuple([x])))

      assert substitute(type, %{x => integer()})
             |> equal?(opt_union(integer(), opt_negation(tuple([integer()]))))
    end

    test "walks tuple, list, map, and function components" do
      x = var(:x)

      type =
        tuple([
          non_empty_list(x, empty_list()),
          closed_map(value: x),
          fun([x], x)
        ])

      expected =
        tuple([
          non_empty_list(integer(), empty_list()),
          closed_map(value: integer()),
          fun([integer()], integer())
        ])

      assert substitute(type, %{x => integer()}) |> equal?(expected)
    end

    test "restores constructor BDD ordering after literal substitution" do
      x = var(:x)
      source = bare_intersection(tuple([x]), tuple([integer()]))
      substituted = substitute(source, %{x => float()})
      rebuilt = bare_intersection(tuple([float()]), tuple([integer()]))

      assert %{tuple: {_, root, child, _, _}} = substituted
      assert root < child
      assert substituted == rebuilt
      assert empty?(substituted)
    end

    test "copies recursive graphs and leaves the source unchanged" do
      x = var(:x)

      %{List: node} =
        recursive(%{
          List: fn recur ->
            opt_union(atom([nil]), tuple([x, recur.(:List)]))
          end
        })

      substituted = substitute(node, %{x => integer()})

      assert vars(node) == MapSet.new([x])
      assert vars(substituted) == MapSet.new()
      assert subtype?(tuple([integer(), atom([nil])]), substituted)
      refute subtype?(tuple([atom(), atom([nil])]), substituted)
    end

    test "preserves sharing when a recursive node occurs more than once" do
      x = var(:x)

      %{List: node} =
        recursive(%{
          List: fn recur -> opt_union(atom([nil]), tuple([x, recur.(:List)])) end
        })

      substituted = substitute(tuple([node, node]), %{x => integer()})

      assert {false, left} = tuple_fetch(substituted, 0)
      assert {false, right} = tuple_fetch(substituted, 1)
      assert left == right
    end

    test "requires variable substitution keys" do
      assert_raise ArgumentError, ~r/expected a type variable/, fn ->
        substitute(var(:x), %{integer() => atom()})
      end
    end

    test "requires static substitution values" do
      x = var(:x)

      assert_raise ArgumentError, ~r/expected a static type/, fn ->
        substitute(x, %{x => dynamic()})
      end
    end
  end

  describe "printing" do
    test "prints variable DNF with the existing type operators" do
      x = var(:x)
      y = var(:y)

      assert to_quoted_string(opt_intersection(x, integer())) == "x and integer()"
      assert to_quoted_string(opt_negation(x)) == "not x"

      printed = to_quoted_string(opt_union(x, opt_intersection(y, integer())))
      assert printed =~ "x"
      assert printed =~ "y"
      assert printed =~ "integer()"
    end

    test "disambiguates identities and invalid variable names" do
      x1 = var(:x)
      x2 = var(:x)

      printed = to_quoted_string(opt_difference(x1, x2))
      assert printed =~ ~r/x__\d+ and not x__\d+/
      refute printed == "x and not x"

      assert to_quoted_string(var(:"bad name")) =~ ~r/type_var__\d+/
    end
  end
end
