defmodule Module.Types.Descr do
  @moduledoc false

  # The descr contains a set-theoretic implementation of types.
  # Types are represented as maps of non-overlapping unions.
  # A bitmap is used to represent non-divisible types. All other
  # types require specific data structures.

  # Vocabulary:
  # DNF: disjunctive normal form (a union of intersections, encoded as a list)
  # BDD: binary decision diagram (a tree representing a type)
  # line: a path from the root of a BDD to a `true` leaf

  # TODO: When we convert from AST to descr, we need to normalize
  # the dynamic type.
  import Bitwise

  @bit_binary 1 <<< 0
  @bit_empty_list 1 <<< 1
  @bit_integer 1 <<< 2
  @bit_float 1 <<< 3
  @bit_pid 1 <<< 4
  @bit_port 1 <<< 5
  @bit_reference 1 <<< 6

  @bit_non_empty_list 1 <<< 7
  @bit_tuple 1 <<< 8
  @bit_fun 1 <<< 9
  @bit_top (1 <<< 10) - 1

  @bit_not_set 1 <<< 10

  @atom_top {:negation, :sets.new(version: 2)}
  @map_top {{:open, %{}}, true, false}

  # Guard helpers

  @term %{bitmap: @bit_top, atom: @atom_top, map: @map_top}
  @none %{}
  @dynamic %{dynamic: @term}

  # Map helpers

  @not_set %{bitmap: @bit_not_set}
  @term_or_not_set %{bitmap: @bit_top ||| @bit_not_set, atom: @atom_top, map: @map_top}

  # Type definitions

  def dynamic(), do: @dynamic
  def term(), do: @term
  def none(), do: @none
  def not_set(), do: @not_set

  def atom(as), do: %{atom: atom_new(as)}
  def atom(), do: %{atom: @atom_top}
  def binary(), do: %{bitmap: @bit_binary}
  def empty_list(), do: %{bitmap: @bit_empty_list}
  def integer(), do: %{bitmap: @bit_integer}
  def float(), do: %{bitmap: @bit_float}
  def fun(), do: %{bitmap: @bit_fun}
  def map(pairs, open_or_closed), do: %{map: map_new(pairs, open_or_closed)}
  def map(pairs), do: %{map: map_new(pairs, :closed)}
  def map(), do: %{map: @map_top}
  def empty_map(), do: map([])
  def non_empty_list(), do: %{bitmap: @bit_non_empty_list}
  def pid(), do: %{bitmap: @bit_pid}
  def port(), do: %{bitmap: @bit_port}
  def reference(), do: %{bitmap: @bit_reference}
  def tuple(), do: %{bitmap: @bit_tuple}

  @boolset :sets.from_list([true, false], version: 2)
  def boolean(), do: %{atom: {:union, @boolset}}

  ## Set operations

  @doc """
  Check type is empty.
  """
  def empty?(descr), do: not not_empty?(descr)
  def term?(descr), do: subtype_static(@term, Map.delete(descr, :dynamic))
  def gradual?(descr), do: is_map_key(descr, :dynamic)

  @doc """
  Computes the union of two descrs.
  """
  def union(%{} = left, %{} = right) do
    is_gradual_left = gradual?(left)
    is_gradual_right = gradual?(right)

    cond do
      is_gradual_left and not is_gradual_right ->
        right_with_dynamic = Map.put(right, :dynamic, right)
        union_static(left, right_with_dynamic)

      is_gradual_right and not is_gradual_left ->
        left_with_dynamic = Map.put(left, :dynamic, left)
        union_static(left_with_dynamic, right)

      true ->
        union_static(left, right)
    end
  end

  defp union_static(left, right) do
    # Erlang maps:merge_with/3 has to preserve the order in combiner.
    # We don't care about the order, so we have a faster implementation.
    if map_size(left) > map_size(right) do
      iterator_union(:maps.next(:maps.iterator(right)), left)
    else
      iterator_union(:maps.next(:maps.iterator(left)), right)
    end
  end

  @compile {:inline, union: 3}
  defp union(:bitmap, v1, v2), do: bitmap_union(v1, v2)
  defp union(:atom, v1, v2), do: atom_union(v1, v2)
  defp union(:dynamic, v1, v2), do: dynamic_union(v1, v2)
  defp union(:map, v1, v2), do: bdd_union(v1, v2)

  @doc """
  Computes the intersection of two descrs.
  """
  def intersection(%{} = left, %{} = right) do
    is_gradual_left = gradual?(left)
    is_gradual_right = gradual?(right)

    cond do
      is_gradual_left and not is_gradual_right ->
        right_with_dynamic = Map.put(right, :dynamic, right)
        intersection_static(left, right_with_dynamic)

      is_gradual_right and not is_gradual_left ->
        left_with_dynamic = Map.put(left, :dynamic, left)
        intersection_static(left_with_dynamic, right)

      true ->
        intersection_static(left, right)
    end
  end

  defp intersection_static(left, right) do
    # Erlang maps:intersect_with/3 has to preserve the order in combiner.
    # We don't care about the order, so we have a faster implementation.
    if map_size(left) > map_size(right) do
      iterator_intersection(:maps.next(:maps.iterator(right)), left, [])
    else
      iterator_intersection(:maps.next(:maps.iterator(left)), right, [])
    end
  end

  # Returning 0 from the callback is taken as none() for that subtype.
  @compile {:inline, intersection: 3}
  defp intersection(:bitmap, v1, v2), do: bitmap_intersection(v1, v2)
  defp intersection(:atom, v1, v2), do: atom_intersection(v1, v2)
  defp intersection(:dynamic, v1, v2), do: dynamic_intersection(v1, v2)
  defp intersection(:map, v1, v2), do: bdd_intersection(v1, v2)

  @doc """
  Computes the difference between two types.
  """
  def difference(left = %{}, right = %{}) do
    if gradual?(left) or gradual?(right) do
      {left_dynamic, left_static} = Map.pop(left, :dynamic, left)
      {right_dynamic, right_static} = Map.pop(right, :dynamic, right)
      dynamic_part = difference_static(left_dynamic, right_static)

      if empty?(dynamic_part),
        do: @none,
        else: Map.put(difference_static(left_static, right_dynamic), :dynamic, dynamic_part)
    else
      difference_static(left, right)
    end
  end

  # For static types, the difference is component-wise.
  defp difference_static(left, right) do
    iterator_difference(:maps.next(:maps.iterator(right)), left)
  end

  # Returning 0 from the callback is taken as none() for that subtype.
  @compile {:inline, difference: 3}
  defp difference(:bitmap, v1, v2), do: bitmap_difference(v1, v2)
  defp difference(:atom, v1, v2), do: atom_difference(v1, v2)
  defp difference(:dynamic, v1, v2), do: dynamic_difference(v1, v2)
  defp difference(:map, v1, v2), do: bdd_difference(v1, v2)

  @doc """
  Compute the negation of a type.
  """
  def negation(%{} = descr), do: difference(term(), descr)

  @doc """
  Check if a type is non-empty. For gradual types, check that the upper bound
  (the dynamic part) is non-empty. Stop as soon as one non-empty component is found.
  Simpler components (bitmap, atom) are checked first for speed since, if they are
  present, the type is non-empty as we normalize then during construction.
  """
  def not_empty?(%{} = descr) do
    descr = Map.get(descr, :dynamic, descr)

    descr != @none and
      (Map.has_key?(descr, :bitmap) or Map.has_key?(descr, :atom) or
         (Map.has_key?(descr, :map) and map_not_empty?(descr.map)))
  end

  @doc """
  Converts a descr to its quoted representation.
  """
  def to_quoted(%{} = descr) do
    case Enum.flat_map(descr, fn {key, value} -> to_quoted(key, value) end) do
      [] -> {:none, [], []}
      unions -> unions |> Enum.sort() |> Enum.reduce(&{:or, [], [&2, &1]})
    end
  end

  @compile {:inline, to_quoted: 2}
  defp to_quoted(:bitmap, val), do: bitmap_to_quoted(val)
  defp to_quoted(:atom, val), do: atom_to_quoted(val)
  defp to_quoted(:dynamic, descr), do: dynamic_to_quoted(descr)
  defp to_quoted(:map, bdd), do: map_to_quoted(bdd)

  @doc """
  Converts a descr to its quoted string representation.
  """
  def to_quoted_string(descr) do
    descr
    |> to_quoted()
    |> Code.Formatter.to_algebra()
    |> Inspect.Algebra.format(98)
    |> IO.iodata_to_binary()
  end

  ## Iterator helpers

  defp iterator_union({key, v1, iterator}, map) do
    acc =
      case map do
        %{^key => v2} -> %{map | key => union(key, v1, v2)}
        %{} -> Map.put(map, key, v1)
      end

    iterator_union(:maps.next(iterator), acc)
  end

  defp iterator_union(:none, map), do: map

  defp iterator_intersection({key, v1, iterator}, map, acc) do
    acc =
      case map do
        %{^key => v2} ->
          case intersection(key, v1, v2) do
            0 -> acc
            value -> [{key, value} | acc]
          end

        %{} ->
          acc
      end

    iterator_intersection(:maps.next(iterator), map, acc)
  end

  defp iterator_intersection(:none, _map, acc), do: :maps.from_list(acc)

  defp iterator_difference({key, v2, iterator}, map) do
    acc =
      case map do
        %{^key => v1} ->
          case difference(key, v1, v2) do
            0 -> Map.delete(map, key)
            value -> %{map | key => value}
          end

        %{} ->
          map
      end

    iterator_difference(:maps.next(iterator), acc)
  end

  defp iterator_difference(:none, map), do: map

  ## Type relations

  @doc """
  Check if a type is a subtype of another.

  If     `left  = (left_dyn  and dynamic()) or left_static`
  and    `right = (right_dyn and dynamic()) or right_static`

  then the gradual subtyping relation defined in Definition 6.5 page 125 of
  the thesis https://vlanvin.fr/papers/thesis.pdf is:

  `left <= right` if and only if
    - `left_static <= right_static`
    - `left_dyn <= right_dyn`

  Because of the dynamic/static invariant in the `descr`, subtyping can be
  simplified in several cases according to which type is gradual or not.
  """
  def subtype?(%{} = left, %{} = right) do
    is_grad_left = gradual?(left)
    is_grad_right = gradual?(right)

    cond do
      is_grad_left and not is_grad_right ->
        left_dynamic = Map.get(left, :dynamic)
        subtype_static(left_dynamic, right)

      is_grad_right and not is_grad_left ->
        right_static = Map.delete(right, :dynamic)
        subtype_static(left, right_static)

      true ->
        subtype_static(left, right)
    end
  end

  defp subtype_static(left, right), do: empty?(difference_static(left, right))

  @doc """
  Check if a type is equal to another.

  It is currently not optimized. Only to be used in tests.
  """
  def equal?(left, right) do
    left == right or (subtype?(left, right) and subtype?(right, left))
  end

  @doc """
  Check if two types have a non-empty intersection.
  """
  def intersect?(left, right), do: not_empty?(intersection(left, right))

  @doc """
  Checks if a type is a compatible subtype of another.

  If `input_type` has a static part (i.e., values that are known to appear and
  need to be handled), then to be compatible it should be a subtype of the
  the dynamic part of `expected_type` (that is, the largest allowed type at
  runtime).

  If `input_type` is a dynamic type, then we check that the two can intersect
  at runtime, i.e. it is possible to get valid inputs at runtime.

  The function is used, in gradual mode, to type an operator that expects a given
  type. For instance, `+` expects `integer() or float()` inputs. Compatible inputs
  include `dynamic()`, `integer()`, but also `dynamic() and (integer() or atom())`.
  Incompatible subtypes include `integer() or list()`, `dynamic() and atom()`.
  """
  def compatible?(input_type, expected_type) do
    {input_dynamic, input_static} = Map.pop(input_type, :dynamic, input_type)
    expected_dynamic = Map.get(expected_type, :dynamic, expected_type)

    if not empty?(input_static) do
      subtype_static(input_static, expected_dynamic)
    else
      intersect?(input_dynamic, expected_dynamic)
    end
  end

  ## Bitmaps

  defp bitmap_union(v1, v2), do: v1 ||| v2
  defp bitmap_intersection(v1, v2), do: v1 &&& v2
  defp bitmap_difference(v1, v2), do: v1 - (v1 &&& v2)

  defp bitmap_to_quoted(val) do
    pairs =
      [
        binary: @bit_binary,
        empty_list: @bit_empty_list,
        integer: @bit_integer,
        float: @bit_float,
        pid: @bit_pid,
        port: @bit_port,
        reference: @bit_reference,
        non_empty_list: @bit_non_empty_list,
        tuple: @bit_tuple,
        fun: @bit_fun
      ]

    for {type, mask} <- pairs,
        (mask &&& val) !== 0,
        do: {type, [], []}
  end

  ## Atoms

  # The atom component of a type consists of pairs `{tag, set}` where `set` is a
  # set of atoms.
  # If `tag = :union` the pair represents the union of the atoms in `set`.
  # Else, if `tag = :negation`, it represents every atom except those in `set`.
  #
  # Example:
  #   - `{:union, :sets.from_list([:a, :b])}` represents type `:a or :b`
  #   - `{:negation, :sets.from_list([:c, :d])}` represents type `atom() \ (:c or :d)
  #
  # `{:negation, :sets.new()}` is the `atom()` top type, as it is the difference
  # of `atom()` with an empty list.
  #
  # `{:union, :sets.new()}` is the empty type for atoms, as it is the union of
  # an empty list of atoms. It is simplified to `0` in set operations, and the key
  # is removed from the map.

  defp atom_new(as) when is_list(as), do: {:union, :sets.from_list(as, version: 2)}

  defp atom_intersection({tag1, s1}, {tag2, s2}) do
    {tag, s} =
      case {tag1, tag2} do
        {:union, :union} -> {:union, :sets.intersection(s1, s2)}
        {:negation, :negation} -> {:negation, :sets.union(s1, s2)}
        {:union, :negation} -> {:union, :sets.subtract(s1, s2)}
        {:negation, :union} -> {:union, :sets.subtract(s2, s1)}
      end

    if tag == :union and :sets.size(s) == 0, do: 0, else: {tag, s}
  end

  defp atom_union({:union, s1}, {:union, s2}), do: {:union, :sets.union(s1, s2)}
  defp atom_union({:negation, s1}, {:negation, s2}), do: {:negation, :sets.intersection(s1, s2)}
  defp atom_union({:union, s1}, {:negation, s2}), do: {:negation, :sets.subtract(s2, s1)}
  defp atom_union({:negation, s1}, {:union, s2}), do: {:negation, :sets.subtract(s1, s2)}

  defp atom_difference({tag1, s1}, {tag2, s2}) do
    {tag, s} =
      case {tag1, tag2} do
        {:union, :union} -> {:union, :sets.subtract(s1, s2)}
        {:negation, :negation} -> {:union, :sets.subtract(s2, s1)}
        {:union, :negation} -> {:union, :sets.intersection(s1, s2)}
        {:negation, :union} -> {:negation, :sets.union(s1, s2)}
      end

    if tag == :union and :sets.size(s) == 0, do: 0, else: {tag, s}
  end

  defp literal(lit), do: {:__block__, [], [lit]}

  defp atom_to_quoted({:union, a}) do
    if :sets.is_subset(@boolset, a) do
      :sets.subtract(a, @boolset)
      |> :sets.to_list()
      |> Enum.sort()
      |> Enum.reduce({:boolean, [], []}, &{:or, [], [&2, literal(&1)]})
    else
      :sets.to_list(a)
      |> Enum.sort()
      |> Enum.map(&literal/1)
      |> Enum.reduce(&{:or, [], [&2, &1]})
    end
    |> List.wrap()
  end

  defp atom_to_quoted({:negation, a}) do
    if :sets.size(a) == 0 do
      {:atom, [], []}
    else
      atom_to_quoted({:union, a})
      |> Kernel.then(&{:and, [], [{:atom, [], []}, {:not, [], &1}]})
    end
    |> List.wrap()
  end

  ## Dynamic

  # A type with a dynamic component is a gradual type; without, it is a static
  # type. The dynamic component itself is a static type; hence, any gradual type
  # can be written using a pair of static types as the union:
  #
  # `type = (dynamic_component and dynamic()) or static_component`
  #
  # where the `static_component` is simply the rest of the `descr`, and `dynamic()`
  # is the base type that can represent any value at runtime. The dynamic and
  # static parts can be considered separately for a mixed-typed analysis. For
  # example, the type
  #
  # `type = (dynamic() and integer()) or boolean()`
  #
  # denotes an expression that evaluates to booleans or integers; however, there is
  # uncertainty about the source of these integers. In static mode, the
  # type-checker refuses to apply a function of type `boolean() -> boolean()` to
  # this argument (since the argument may turn out to be an integer()), but in
  # dynamic mode, it considers the type obtained by replacing `dynamic()` with
  # `none()` (that is, `boolean()`), accepts the application, but types it with a
  # type that contains `dynamic()`.
  #
  # When pattern matching on an expression of type `type`, the static part (here,
  # booleans) has to be handled exhaustively. In contrast, the dynamic part can
  # produce potential warnings in specific user-induced conditions, such as asking
  # for stronger enforcement of static types.
  #
  # During construction and through set operations, we maintain the invariant that
  # the dynamic component is a supertype of the static one, formally
  # `dynamic_component >= static_component`
  #
  # With this invariant, the dynamic component always represents every value that
  # a given gradual type can take at runtime, allowing us to simplify set operations,
  # compared, for example, to keeping only the extra dynamic type that can obtained
  # on top of the static type. Though, the latter may be used for printing purposes.
  #
  # There are two ways for a descr to represent a static type: either the
  # `:dynamic` field is not_set, or it contains a type equal to the static component
  # (that is, there are no extra dynamic values).

  defp dynamic_intersection(left, right) do
    inter = intersection_static(left, right)
    if empty?(inter), do: 0, else: inter
  end

  defp dynamic_difference(left, right) do
    diff = difference_static(left, right)
    if empty?(diff), do: 0, else: diff
  end

  defp dynamic_union(left, right), do: union_static(left, right)

  defp dynamic_to_quoted(%{} = descr) do
    cond do
      term?(descr) -> [{:dynamic, [], []}]
      single = indivisible_bitmap(descr) -> [single]
      true -> [{:and, [], [{:dynamic, [], []}, to_quoted(descr)]}]
    end
  end

  defp indivisible_bitmap(descr) do
    with %{bitmap: bitmap} when map_size(descr) == 1 <- descr,
         [single] <- bitmap_to_quoted(bitmap) do
      single
    else
      _ -> nil
    end
  end

  ## Not_set

  # `not_set()` is a special base type that represents an absent field in a map.
  # E.g., `%{a: integer(), b: not_set(), ...}` represents a map with an integer
  # field `a` and an absent field `b`, and possibly other fields.
  # When writing down a map type, specifying a key as optional is syntactic sugar
  # for specifying the key as a union of the key type and `not_set()`. For example,
  # `%{optional(:foo) => integer()}` is equivalent to `%{:foo => integer() or not_set()}`,
  # which can also be written `%{:foo => if_set(integer())}`.

  # `not_set()` has no meaning outside of map types.

  # Add the not_set type to `type`
  def if_set(type), do: Map.update(type, :bitmap, @bit_not_set, &(&1 ||| @bit_not_set))
  defp has_not_set?(type), do: (Map.get(type, :bitmap, 0) &&& @bit_not_set) != 0

  defp remove_not_set(type) do
    case type do
      %{:bitmap => @bit_not_set} -> Map.delete(type, :bitmap)
      %{:bitmap => bitmap} -> Map.put(type, :bitmap, bitmap &&& ~~~@bit_not_set)
      _ -> type
    end
  end

  ## Map

  # Map types are stored in a tree (binary decision diagram) that contains
  # map literals at the nodes.
  #
  # A map literal is a pair `{tag, fields}` where
  #   - `tag` is either `:open` or `:closed`.
  #   - `fields` is a map that associates key values with types
  #
  # The tree encodes arbitrary unions and intersections of map literals. For example,
  # the intersection of the closed map `%{a: integer()}` with the closed map
  # `%{a: atom()}` is stored in the tree
  #
  #                           {:closed, %{a: integer()}}
  #                          /                         \
  #          {:closed, %{a: atom()}}                  false
  #         /                       \
  #       true                    false
  #
  # To see the type represented by this tree, start from the root and find every
  # path to `true` leaves. Each path represents the intersection of its map
  # literals, where each literal is either taken positively if followed by a
  # left edge, or negated if followed by a right edge.
  #
  # For example, this similar tree
  #
  #                           {:closed, %{a: integer()}}
  #                          /                         \
  #          {:closed, %{a: atom()}}                  false
  #         /                       \
  #       true                      true
  #
  # represents the union of (the intersection of `%{a: integer()}` and `%{a: atom()}`)
  # with (the intersection of `%{a: integer()}` and `not %{a: atom()}`).
  #
  # TODO: add domain key types https://www.irif.fr/~gc/papers/icfp23.pdf
  # and adapt the constructors to support them.

  # Creates a map literal. Keys have to be values.
  defp map_new(pairs, open_or_closed) do
    fields =
      Map.new(pairs, fn
        {{:optional, [], [key]}, type} -> {key, if_set(type)}
        {key, type} -> {key, type}
      end)

    bdd_new({open_or_closed, fields})
  end

  defp descr_map_make(tag, fields), do: %{map: bdd_new({tag, fields})}

  @doc """
  Gets the type of the value returned by accessing `key` on `map`.
  Does not guarantee the key exists. To do that, use `map_has_key?`.
  """
  def map_get!(%{} = descr, key) do
    if not gradual?(descr) do
      map_get_static(descr, key)
    else
      {dynamic, static} = Map.pop(descr, :dynamic)
      dynamic_value_type = map_get_static(dynamic, key)
      static_value_type = map_get_static(static, key)
      union(intersection(dynamic(), dynamic_value_type), static_value_type)
    end
  end

  @doc """
  Check that a key is present.
  """
  def map_has_key?(descr, key) do
    subtype?(descr, map([{key, term()}], :open))
  end

  @doc """
  Check that a key may be present.
  """
  def map_may_have_key?(descr, key) do
    compatible?(descr, map([{key, term()}], :open))
  end

  @doc """
  Gets the set of keys that are always present in a map.
  TODO: make it using on map_split_on_key
  """
  def map_keys(%{} = descr) do
    if subtype?(descr, map()) do
      # does not work for input none()
      Map.get(descr, :dynamic, descr).map
      |> map_get_dnf()
      |> process_list(
        fn {:map, [fields, _, _]} ->
          :sets.from_list(for({key, {false, _}} <- fields, do: key), version: 2)
        end,
        &:sets.intersection(&1, &2)
      )
      |> Kernel.then(&%{atom: {:union, &1}})
    else
      atom([])
    end
  end

  defp process_list([single_element], f, _combine), do: f.(single_element)

  defp process_list(list, f, combine) do
    [head | tail] = list
    initial_acc = f.(head)
    Enum.reduce(tail, initial_acc, fn element, acc -> combine.(acc, f.(element)) end)
  end

  # Assuming `descr` is a static type. Accessing `key` will, if it succeeds,
  # return a value of the type returned. To guarantee that the key is always
  # present, use `map_has_key?`. To guarantee that the key may be present
  # use `map_may_have_key?`. If key is never present, result will be `none()`.
  defp map_get_static(descr, key) do
    descr_map = intersection(descr, map())

    if empty?(descr_map) do
      none()
    else
      map_split_on_key(descr_map.map, key)
      |> Enum.reduce(none(), fn {typeof_key, _}, union -> union(typeof_key, union) end)
      |> remove_not_set()
    end
  end

  # Given a map bdd, normalizes it into a union of maps of the form
  #                {:map, [fields, is_open, has_empty]}
  #
  # For each key in the bdd, transform the dnf of the map into a dnf of pairs
  # `{value_type, rest_of_map}` where `key` is removed from `rest_of_map`.
  # Each `key` produces a dnf of pairs, that is each time normalized (into a
  # disjoint union of pairs) as part of `map_split_on_key`. The result is used
  defp map_get_dnf(d), do: map_get_dnf(d, [])

  defp map_get_dnf(d, fields_acc) do
    case find_key(d) do
      # `d` is a map bdd with no named fields (i.e., only %{..} or %{} appear at the nodes)
      nil ->
        {is_open, has_empty} = empty_cases(d)

        if is_open or has_empty,
          do: [{:map, [Enum.sort(fields_acc), is_open, has_empty]}],
          else: []

      {:key, key} ->
        # Split the map on the found key; for each possible split, recurse
        # on the rest of the map (which does not contain the key anymore)
        map_split_on_key(d, key)
        |> Enum.flat_map(fn {value_type, rest_of_map} ->
          type_with_option = {has_not_set?(value_type), remove_not_set(value_type)}
          map_get_dnf(rest_of_map.map, [{key, type_with_option} | fields_acc])
        end)
    end
  end

  # defp map_bdd_fold(bdd, seen, acc, fun) do
  #   {{_tag, fields}, left, right} when fields != %{} ->
  # acc = :maps.fold(fields, acc, fun)
  # acc = map_bdd_fold(left, seen, acc, fun)
  # map_bdd_fold(right, seen, acc, fun)
  # end

  # def map_emptiness() do
  #   map_fold(bdd, [], fn key, acc ->
  #     throw :omg
  #   end)
  #   catch
  #     :omg -> fase
  #   end
  # end

  # When i do emptiness, just send a throw

  # Finds a defined key in the `bdd` representing a map, or returns `nil`
  defp find_key(bdd) do
    case bdd do
      true -> nil

      false -> nil
      {{_tag, fields}, _, _} when map_size(fields) != 0 -> {:key, Map.keys(fields) |> hd()}
      {_, left_bdd, right_bdd} -> find_key(left_bdd) || find_key(right_bdd)
    end
  end

  # Given a map bdd with no named fields, returns a pair of booleans
  # `{is_open, has_empty}` where `is_open` is true if the map is open, and
  # `has_empty` is true if it contains the empty map.
  # For example, `%{...}` returns `{true, true}`, `%{}` returns `{false, true}`,
  # and `%{...} and not %{}` returns `{true, false}`.
  defp empty_cases(bdd) do
    case bdd do
      true ->
        {true, true}

      false ->
        {false, false}

      {{tag, fields}, left, right} ->
        {b1, b2} =
          cond do
            map_size(fields) != 0 -> raise "`empty_cases` called on non-empty map"
            tag == :open -> {true, true}
            tag == :closed -> {false, true}
          end

        {c1, c2} = empty_cases(left)
        {d1, d2} = empty_cases(right)
        {(b1 and c1) or (not b1 and d1), (b2 and c2) or (not b2 and d2)}
    end
  end

  # Idea: maybe build everything on top of the shape dnf b/c we are converting
  # to it anyway

  # Takes a map bdd and a key, and returns an equivalent dnf of pairs.
  # See `split_line_on_key/5`.
  defp map_split_on_key(d, key) do
    bdd_get(d)
    |> Enum.flat_map(fn {pos, neg} -> split_line_on_key(pos, neg, key, [], []) end)
    |> pair_simplify_dnf(@term_or_not_set)
  end

  # Given a line, that is, a list `positive` of map literals and `negative` of
  # negated map literals, and a `key`, splits every map literal on the key and
  # outputs a DNF of pairs, that is, a list (union) of lists (intersections) of pairs.
  defp split_line_on_key([], [], _, pos_acc, neg_acc), do: [{pos_acc, neg_acc}]

  defp split_line_on_key([map_literal | positive], negative, key, pos_acc, neg_acc) do
    case single_split(map_literal, key) do
      # { .. } the open map in a positive intersection can be ignored
      :no_split ->
        split_line_on_key(positive, negative, key, pos_acc, neg_acc)

      # {typeof l, rest} is added to the positive accumulator
      {value_type, rest_of_map} ->
        split_line_on_key(positive, negative, key, [{value_type, rest_of_map} | pos_acc], neg_acc)
    end
  end

  defp split_line_on_key([], [map_literal | negative], key, pos_acc, neg_acc) do
    case single_split(map_literal, key) do
      # an intersection that contains %{...} is empty, so we discard it entirely
      :no_split ->
        []

      # {typeof l, rest_of_map} is added to the negative accumulator
      {value_type, rest_of_map} ->
        split_line_on_key([], negative, key, pos_acc, [{value_type, rest_of_map} | neg_acc])
    end
  end

  # Splits a map literal on a key. This means that given a map literal, compute
  # the pair of types `{value_type, rest_of_map}` where `value_type` is the type
  # associated with `key`, and `rest_of_map` is obtained by removing `key`.
  defp single_split({tag, fields}, key) do
    {value_type, rest_of_map} = Map.pop(fields, key)

    cond do
      value_type != nil -> {value_type, descr_map_make(tag, rest_of_map)}
      tag == :closed -> {@not_set, descr_map_make(tag, rest_of_map)}
      # case where there is an open map with no keys { .. }
      map_size(fields) == 0 -> :no_split
      true -> {@term_or_not_set, descr_map_make(tag, rest_of_map)}
    end
  end

  defp map_to_quoted(bdd) do
    case map_get_dnf(bdd) do
      [] ->
        []

      x ->
        Enum.map(x, &map_dnf_to_quoted/1)
        |> Enum.reduce(&{:or, [], [&2, &1]})
        |> List.wrap()
    end
  end

  def map_dnf_to_quoted({:map, [fields, is_open, has_empty]}) do
    case {is_open, has_empty} do
      {false, true} ->
        {:%{}, [], map_literal_to_quoted(fields, is_open)}

      {true, true} ->
        {:%{}, [], [{:..., [], nil} | map_literal_to_quoted(fields, is_open)]}

      {true, false} ->
        {:and, [],
         [
           {:%{}, [], [{:..., [], nil} | map_literal_to_quoted(fields, is_open)]},
           {:not, [], [{:%{}, [], map_literal_to_quoted(fields, is_open)}]}
         ]}
    end
  end

  defp map_literal_to_quoted(map, is_open) do
    for {key, {optional_field?, type}} <- map,
        not (is_open and optional_field? and term?(type)) do
      cond do
        optional_field? and empty?(type) -> {literal(key), {:not_set, [], []}}
        optional_field? -> {literal(key), {:if_set, [], [to_quoted(type)]}}
        true -> {literal(key), to_quoted(type)}
      end
    end
  end

  # Function similar to `map_get_dnf/1` but short-circuits if it finds a non-empty
  # map literal in the union.
  defp map_not_empty?(bdd), do: map_not_empty?(bdd, [])

  defp map_not_empty?(bdd, fields_acc) do
    case find_key(bdd) do
      # `bdd` is a map bdd with no named fields (i.e., only %{..} or %{} appear at the nodes)
      nil ->
        {is_open, has_empty} = empty_cases(bdd)
        is_open or has_empty

      {:key, key} ->
        # Split the map on the found key; for each possible split, recurse
        # on the rest of the map (which does not contain the key anymore)
        map_split_on_key(bdd, key)
        |> Enum.any?(fn {value_type, rest_of_map} ->
          type_with_option = {has_not_set?(value_type), remove_not_set(value_type)}
          map_not_empty?(rest_of_map.map, [{key, type_with_option} | fields_acc])
        end)
    end
  end

  ## BDD (Binary Decision Diagrams)
  #
  # Generic BDD operations. Binary decision diagrams are binary trees used to
  # encode unions of intersections of type literals (e.g., map literals).
  # Set operations are generic tree merges, which use the global ordering of
  # values to approximately balance the tree. Semantic information (such as: is
  # the type empty?) is obtained when needed by extracting the information from
  # the tree and normalizing it (see `map_get_dnf/1` for example).

  defp bdd_new(literal), do: {literal, true, false}

  defp bdd_union(true, _), do: true
  defp bdd_union(_, true), do: true
  defp bdd_union(false, bdd), do: bdd
  defp bdd_union(bdd, false), do: bdd

  defp bdd_union(b1 = {a1, c1, d1}, b2 = {a2, c2, d2}) do
    cond do
      a1 == a2 -> {a1, bdd_union(c1, c2), bdd_union(d1, d2)}
      a1 < a2 -> {a1, bdd_union(c1, b2), bdd_union(d1, b2)}
      a1 > a2 -> {a2, bdd_union(b1, c2), bdd_union(b1, d2)}
    end
  end

  defp bdd_intersection(false, _), do: false
  defp bdd_intersection(_, false), do: false
  defp bdd_intersection(true, bdd), do: bdd
  defp bdd_intersection(bdd, true), do: bdd

  defp bdd_intersection(bdd1 = {val1, left1, right1}, bdd2 = {val2, left2, right2}) do
    cond do
      val1 == val2 -> {val1, bdd_intersection(left1, left2), bdd_intersection(right1, right2)}
      val1 < val2 -> {val1, bdd_intersection(left1, bdd2), bdd_intersection(right1, bdd2)}
      val1 > val2 -> {val2, bdd_intersection(bdd1, left2), bdd_intersection(bdd1, right2)}
    end
  end

  defp bdd_difference(false, _), do: false
  defp bdd_difference(_, true), do: false
  defp bdd_difference(bdd, false), do: bdd

  defp bdd_difference(true, {value, high, low}) do
    {value, bdd_difference(true, high), bdd_difference(true, low)}
  end

  defp bdd_difference(bdd1 = {value1, left1, right1}, bdd2 = {value2, left2, right2}) do
    cond do
      value1 == value2 -> {value1, bdd_difference(left1, left2), bdd_difference(right1, right2)}
      value1 < value2 -> {value1, bdd_difference(left1, bdd2), bdd_difference(right1, bdd2)}
      value1 > value2 -> {value2, bdd_difference(bdd1, left2), bdd_difference(bdd1, right2)}
    end
  end

  # Extracts the union of intersections of literals from a BDD. Every line that
  # starts from the root and ends in a leaf with value `true` represents an intersection
  # of literals (where a literal is positive if the path goes left, and negative
  # if it goes right). The type is the union of all the lines.
  defp bdd_get(bdd), do: bdd_get([], bdd, [], [])

  defp bdd_get(acc, false, _pos, _neg), do: acc
  defp bdd_get(acc, true, pos_acc, neg_acc), do: [{pos_acc, neg_acc} | acc]

  defp bdd_get(acc, {literal, bdd_left, bdd_right}, pos_acc, neg_acc) do
    bdd_get(acc, bdd_right, pos_acc, [literal | neg_acc])
    |> bdd_get(bdd_left, [literal | pos_acc], neg_acc)
  end

  ## Pairs
  #
  # To simplify disjunctive normal forms of e.g., map types, it is useful to
  # convert them into disjunctive normal forms of pairs of types, and define
  # normalization algorithms on pairs.

  # Takes a DNF of pairs and simplifies it into a equivalent single list (union)
  # of type pairs. The `term` argument should be either `@term_or_not_set` (for
  # map value types) or `@term` in general.
  # Remark: all lines of a pair bdd are naturally disjoint, because choosing a
  # different edge means intersect with a literal or its negation.
  defp pair_simplify_dnf(dnf, term) do
    Enum.flat_map(dnf, &pair_simplify_line(&1, term))
  end

  # A line is a bdd path from the root to a `true` leaf. It is initially stored
  # as a list of pairs `{positive, negative}` where `positive` is a list of
  # literals and `negative` is a list of negated literals. Positive pairs can
  # all be intersected component-wise. Negative ones are eliminated iteratively.
  defp pair_simplify_line({positive, negative}, term) do
    {fst, snd} = pair_intersection(positive, term)

    if empty?(fst) or empty?(snd),
      do: [],
      else: make_pairs_disjoint(negative) |> eliminate_negations(fst, snd)
  end

  # TODO:
  # 1) if just one element postivie = [{fst, snd}], dont check emptines
  # 2) if the pos/neg come from splitting, the intersection of rest_of_maps will
  #    never be empty

  # Eliminates negations from `{t, s} and not negative`.
  # Formula:
  #   if `negative` is a union of pairs disjoint on their first component:
  #                 union<i=1..n> {t_i, s_i}
  #   then
  #                 {t, s} and not (union<i=1..n> {t_i, s_i})
  #   is equivalent to
  #                 union<i=1..n> {t and t_i, s and not s_i}
  #                     or {t and not (union{i=1..n} t_i), s}
  # which eliminates all top-level negations and produces a union of pairs
  # that are not empty disjoint on their first component.
  defp eliminate_negations(negative, t, s) do
    {pair_union, union_of_t_i} =
      Enum.reduce(
        negative,
        {[], none()},
        fn {t_i, s_i}, {accu, union_of_t_i} ->
          i = intersection(t, t_i)

          # rem: the condition where this one is empty is good for pretty printing
          # but not for emptiness checking
          j = intersection(s, s_i)

          # discard negative literals that do not intersect with the positive ones
          if not_empty?(i) do
            union_of_t_i = union(union_of_t_i, t_i)
            s_diff = difference(s, s_i)

            if not_empty?(s_diff),
              do: {[{i, s_diff} | accu], union_of_t_i},
              else: {accu, union_of_t_i}
          else
            {accu, union_of_t_i}
          end
        end
      )

    t_diff = difference(t, union_of_t_i)

    if not_empty?(t_diff),
      do: [{t_diff, s} | pair_union],
      else: pair_union
  end

  # Component-wise intersection of a list of pairs.
  defp pair_intersection(pair_list, term) do
    Enum.reduce(pair_list, {term, term}, fn {x1, x2}, {acc1, acc2} ->
      {intersection(acc1, x1), intersection(acc2, x2)}
    end)
  end

  # Inserts a pair of types {fst, snd} into a list of pairs that are disjoint
  # on their first component. The invariant on `acc` is that its elements are
  # two-to-two disjoint with the first argument's `pairs`.
  #
  # To insert {fst, snd} into a disjoint pairs list, we go through the list to find
  # each pair whose first element has a non-empty intersection with `fst`. Then
  # we decompose {fst, snd} over each such pair to produce disjoint ones, and add
  # the decompositions into the accumulator.
  defp add_pair_to_disjoint_list([], fst, snd, acc), do: [{fst, snd} | acc]

  defp add_pair_to_disjoint_list([{s1, s2} | pairs], fst, snd, acc) do
    x = intersection(fst, s1)

    if empty?(x) do
      add_pair_to_disjoint_list(pairs, fst, snd, [{s1, s2} | acc])
    else
      fst_diff = difference(fst, s1)
      s1_diff = difference(s1, fst)
      empty_fst_diff = empty?(fst_diff)
      empty_s1_diff = empty?(s1_diff)

      cond do
        # case fst = s1
        empty_fst_diff and empty_s1_diff ->
          [{x, union(snd, s2)} | Enum.reverse(pairs, acc)]

        # special case: if fst is a subtype of s1, the disjointness invariant
        # ensures we can safely add those two pairs and end the recursion
        empty_fst_diff ->
          [{s1_diff, s2}, {x, union(snd, s2)} | Enum.reverse(pairs, acc)]

        empty_s1_diff ->
          add_pair_to_disjoint_list(pairs, fst_diff, snd, [{x, union(snd, s2)} | acc])

        true ->
          add_pair_to_disjoint_list(pairs, fst_diff, snd, [
            {s1_diff, s2},
            {x, union(snd, s2)} | acc
          ])
      end
    end
  end

  # Makes a union (list) of pairs into an equivalent disjoint union of pairs.
  defp make_pairs_disjoint(pairs) do
    Enum.reduce(pairs, [], fn {t1, t2}, acc -> add_pair_to_disjoint_list(acc, t1, t2, []) end)
  end
end
