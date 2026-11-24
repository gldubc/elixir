# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

Code.require_file("type_helper.exs", __DIR__)

defmodule Module.Types.ListPrintingTest do
  use ExUnit.Case, async: true

  import Module.Types.Descr

  test "list differences with list tails" do
    type =
      non_empty_list(atom([:a, :b]), list(atom([:b, :c])))
      |> bare_difference(non_empty_list(atom([:a])))
      |> bare_difference(non_empty_list(atom([:b, :c]), list(atom([:a, :b]))))

    assert to_quoted_string(type) ==
             """
             non_empty_list(:a or :b, list(:b or :c)) and not non_empty_list(:a) and
               not non_empty_list(:b or :c, list(:a or :b))
             """
             |> String.trim()
  end

  test "excluding one-element lists" do
    type = bare_difference(list(integer()), list_cons(integer(), empty_list()))

    assert to_quoted_string(type) ==
             "empty_list() or list_cons(integer(), non_empty_list(integer()))"
  end

  test "impossible lists print as none()" do
    for type <- [
          list_cons(none(), term()),
          list_cons(integer(), none()),
          list_cons(tuple([none()]), empty_list()),
          bare_intersection(list_cons(integer(), empty_list()), list_cons(atom(), empty_list())),
          bare_difference(list_cons(integer(), empty_list()), list_cons(integer(), term()))
        ] do
      assert to_quoted_string(type) == "none()"
      assert to_quoted_string(dynamic(type)) == "none()"
    end
  end

  test "unions with an empty type" do
    empty = list_cons(integer(), none())
    inhabited = list_cons(atom(), empty_list())

    assert to_quoted_string(list(none())) == "empty_list()"
    assert to_quoted_string(bare_union(empty, inhabited)) == "list_cons(atom(), empty_list())"
  end

  test "intersecting two recursive lists" do
    type = bare_intersection(list(integer()), list(term()))

    assert to_quoted_string(type) == "list(integer())"
  end

  test "intersections and differences fold into one list" do
    int_or_empty = opt_union(integer(), empty_list())

    type =
      bare_intersection(
        non_empty_list(atom([:a, :b]), int_or_empty),
        non_empty_list(atom([:b, :c]), integer())
      )

    assert equal?(type, non_empty_list(atom([:b]), integer()))
    assert to_quoted_string(type) == "non_empty_list(:b, integer())"

    # Disjoint endings leave no list.
    type = bare_intersection(non_empty_list(atom([:a])), non_empty_list(atom([:a]), integer()))
    assert to_quoted_string(type) == "none()"

    # A larger excluded head removes its endings.
    type =
      bare_difference(
        non_empty_list(atom([:a]), int_or_empty),
        non_empty_list(atom([:a, :b]), integer())
      )

    assert equal?(type, non_empty_list(atom([:a])))
    assert to_quoted_string(type) == "non_empty_list(:a)"

    # A smaller excluded head cannot remove them.
    type =
      bare_difference(
        non_empty_list(atom([:a, :b]), int_or_empty),
        non_empty_list(atom([:a]), integer())
      )

    assert to_quoted_string(type) ==
             "non_empty_list(:a or :b, empty_list() or integer()) and not non_empty_list(:a, integer())"
  end

  describe "empty list folding" do
    test "folds into every proper-list branch" do
      type =
        list(atom([:a, :b, :c]))
        |> opt_difference(non_empty_list(atom([:a, :b])))
        |> opt_union(list(integer()))

      assert to_quoted_string(type) ==
               "(list(:a or :b or :c) and not non_empty_list(:a or :b)) or list(integer())"

      assert subtype?(empty_list(), type)
    end

    test "requires the empty list" do
      type = bare_union(non_empty_list(atom()), non_empty_list(integer()))
      assert to_quoted_string(type) == "non_empty_list(atom()) or non_empty_list(integer())"
    end

    test "skips branches with other endings" do
      type =
        empty_list()
        |> opt_union(non_empty_list(atom(), integer()))
        |> opt_union(non_empty_list(integer()))

      assert to_quoted_string(type) ==
               "list(integer()) or non_empty_list(atom(), integer())"

      type = opt_union(empty_list(), non_empty_list(atom(), integer()))
      assert to_quoted_string(type) == "empty_list() or non_empty_list(atom(), integer())"
    end

    test "applies to the dynamic part" do
      type = dynamic(bare_union(list(atom()), list(integer())))
      assert to_quoted_string(type) == "dynamic(list(atom()) or list(integer()))"
    end
  end

  test "recursive lists" do
    %{ints: ints, atoms: atoms} =
      recursive(%{
        ints: fn recur -> bare_union(empty_list(), list_cons(integer(), recur.(:ints))) end,
        atoms: fn recur ->
          bare_union(list_cons(atom(), empty_list()), list_cons(atom(), recur.(:atoms)))
        end
      })

    assert to_quoted_string(ints) == "list(integer())"
    assert to_quoted_string(list_cons(integer(), ints)) == "non_empty_list(integer())"
    assert to_quoted_string(atoms) == "non_empty_list(atom())"
  end

  test "recursive non-empty lists" do
    for head <- [integer(), atom(), tuple(List.duplicate(integer(), 160))] do
      node =
        recursive(%{
          x: fn recur -> bare_union(empty_list(), non_empty_list(head, recur.(:x))) end
        }).x

      assert to_quoted_string(node) == to_quoted_string(list(head))

      assert to_quoted_string(non_empty_list(head, node)) ==
               to_quoted_string(non_empty_list(head))

      assert to_quoted_string(dynamic(unfold(node))) == to_quoted_string(dynamic(list(head)))
    end
  end

  test "recursion inside a large list element" do
    node =
      recursive(%{
        x: fn recur ->
          head =
            tuple(List.duplicate(integer(), 160) ++ [closed_map(nested: {recur.(:x), false})])

          bare_union(empty_list(), non_empty_list(head, recur.(:x)))
        end
      }).x

    assert {:recur, _, [var, body]} = to_quoted(node)

    assert {:or, _, [{:empty_list, _, []}, {:non_empty_list, _, [{:{}, _, fields}, ^var]}]} =
             body

    assert {:%{}, _, [{_, ^var}]} = List.last(fields)
  end

  test "integer elements with an atom-list tail" do
    type = non_empty_list(integer(), list(atom()))

    assert to_quoted_string(type) == "non_empty_list(integer(), list(atom()))"
  end

  test "union of atom lists and integer lists" do
    type = bare_union(list(atom()), list(integer()))

    # The empty list folds into every proper-list branch.
    assert to_quoted_string(type) == "list(atom()) or list(integer())"
  end

  test "two-element list" do
    type = list_cons(integer(), list_cons(integer(), empty_list()))

    assert to_quoted_string(type) ==
             "list_cons(integer(), list_cons(integer(), empty_list()))"
  end

  test "lists of alternating integers and atoms" do
    node =
      recursive(%{
        x: fn recur ->
          bare_union(empty_list(), list_cons(integer(), list_cons(atom(), recur.(:x))))
        end
      }).x

    assert to_quoted_string(node) ==
             "recur(t1, empty_list() or list_cons(integer(), list_cons(atom(), t1)))"
  end

  describe "roll_lists: true" do
    test "is opt-in" do
      type = list_cons(integer(), list_cons(integer(), empty_list()))

      assert to_quoted_string(type) ==
               "list_cons(integer(), list_cons(integer(), empty_list()))"

      assert to_quoted_string(type, roll_lists: false) == to_quoted_string(type)
      assert to_quoted_string(type, roll_lists: true) == "non_empty_list(integer())"
    end

    test "prints sound over-approximations" do
      alternating =
        recursive(%{
          x: fn recur ->
            bare_union(empty_list(), list_cons(integer(), list_cons(atom(), recur.(:x))))
          end
        }).x

      tails =
        non_empty_list(atom([:a, :b]), list(atom([:b, :c])))
        |> bare_difference(non_empty_list(atom([:a])))
        |> bare_difference(non_empty_list(atom([:b, :c]), list(atom([:a, :b]))))

      for {type, rolled, printed} <- [
            {alternating, list(opt_union(atom(), integer())), "list(atom() or integer())"},
            {opt_difference(list(term()), list(integer())), non_empty_list(term()),
             "non_empty_list(term())"},
            {tails, non_empty_list(atom([:a, :b, :c])), "non_empty_list(:a or :b or :c)"}
          ] do
        assert to_quoted_string(type, roll_lists: true) == printed
        assert subtype?(type, rolled)
      end
    end

    test "keeps recognized lists exact" do
      assert to_quoted_string(list(integer()), roll_lists: true) == "list(integer())"

      assert to_quoted_string(non_empty_list(integer(), atom([:a])), roll_lists: true) ==
               "non_empty_list(integer(), :a)"
    end

    test "applies inside other types" do
      type = tuple([list_cons(integer(), list_cons(atom(), empty_list()))])

      assert to_quoted_string(type) ==
               "{list_cons(integer(), list_cons(atom(), empty_list()))}"

      assert to_quoted_string(type, roll_lists: true) == "{non_empty_list(atom() or integer())}"
    end
  end
end
