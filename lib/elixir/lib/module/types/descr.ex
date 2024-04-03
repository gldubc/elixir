defmodule Module.Types.Descr do
  @moduledoc false

  # The descr contains a set-theoretic implementation of types.
  # Types are represented as maps of non-overlapping unions.
  # A bitmap is used to represent non-divisible types. All other
  # types require specific data structures.

  # Vocabulary:
  # DNF: disjunctive normal form
  # BDD: binary decision diagram

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

  @bit_undef 1 <<< 10

  @atom_top {:negation, :sets.new(version: 2)}
  @map_top {{:open, %{}}, true, false}

  # Guard helpers

  @term %{bitmap: @bit_top, atom: @atom_top, map: @map_top}
  @none %{}
  @dynamic %{dynamic: @term}

  # Map helpers

  @undef %{bit: @bit_undef}
  @term_or_undef %{bitmap: @bit_top ||| @bit_undef, atom: @atom_top, map: @map_top}

  # Type definitions

  def dynamic(), do: @dynamic
  def term(), do: @term
  def none(), do: @none

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
  def empty?(descr), do: descr == @none or not not_empty?(descr)
  def term?(descr), do: Map.delete(descr, :dynamic) == @term or subtype?(@term, descr)
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
  Check if a type is non-empty. For gradual types, check that the upper bound (in the dynamic part)
  is non-empty.
  """
  def not_empty?(%{} = descr) do
    iterator_not_empty(:maps.next(:maps.iterator(Map.get(descr, :dynamic, descr))))
  end

  # If `:bitmap` or `:atom` are set, the type is non-empty since we normalize
  # them during construction.
  @compile {:inline, not_empty?: 1}
  def not_empty?(:bitmap, _val), do: true
  def not_empty?(:atom, _val), do: true
  def not_empty?(:map, bdd), do: map_not_empty?(bdd)

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

  defp iterator_not_empty({key, v, iterator}) do
    if not_empty?(key, v), do: true, else: iterator_not_empty(:maps.next(iterator))
  end

  defp iterator_not_empty(:none), do: false

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

  # Dynamic
  #
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
  # `:dynamic` field is unset, or it contains a type equal to the static component
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

  # Unset special type.

  # Add the unset type to `type`
  def or_unset(type), do: Map.update(type, :bitmap, @bit_undef, &(&1 ||| @bit_undef))

  def contains_unset?(type), do: (Map.get(type, :bitmap, 0) &&& @bit_undef) !== 0

  def remove_unset(type) do
    case type do
      %{:bitmap => @bit_undef} -> Map.delete(type, :bitmap)
      %{:bitmap => bitmap} -> Map.put(type, :bitmap, bitmap &&& ~~~@bit_undef)
      _ -> type
    end
  end

  # Map
  #
  # Map operations.

  defp map_new(pairs, open_or_closed) do
    fields =
      Map.new(pairs, fn
        {{:optional, [], [key]}, type} -> {key, or_unset(type)}
        {key, type} -> {key, type}
      end)

    bdd_new({open_or_closed, fields})
  end

  defp map_make(tag, fields), do: %{map: bdd_new({tag, fields})}

  defp map_not_empty?(bdd), do: map_get_dnf(bdd) |> check_map()

  defp check_map([]), do: false
  defp check_map(list) when is_list(list), do: true

  # Returns a normalized DNF representation of a map type, that is, a union of map literals.
  # The algorithm goes through every possible field (label) in the map.
  # For each label found, we transform the disjunctive normal form of the
  # map into a disjunctive normal form of pairs `{typeof label, rest_of_map}`
  # where the field `label` is removed from `rest_of_map`.
  # Each `label` produces a DNF of pairs, that is each time normalized (that is,
  # simplified into a union of pairs disjoint on their first component)
  # as part of `map_split_on_label`. The result is then used to produce
  # a single list that is a union of map literals of the form `{:map_literal, [fields, is_open, has_empty]}`
  def map_get_dnf(d), do: map_get_dnf(d, [])

  defp map_get_dnf(d, fields_acc) do
    case find_label(d) do
      # `d` is a map bdd with no named fields (i.e., only %{..} or %{} appear at the nodes)
      nil ->
        {is_open, has_empty} = empty_cases(d)

        if is_open or has_empty,
          do: [{:map_literal, [Enum.sort(fields_acc), is_open, has_empty]}],
          else: []

      {:label, label} ->
        # Split the map on the found label; for each possible split, recurse
        # on the rest of the map (which does not contain the label anymore)
        map_split_on_label(d, label)
        |> Enum.flat_map(fn {label_type, rest_of_map} ->
          type_with_option = {contains_unset?(label_type), remove_unset(label_type)}
          map_get_dnf(rest_of_map.map, [{label, type_with_option} | fields_acc])
        end)
    end
  end

  # Finds a defined label in the `bdd` representing a map, or returns `nil`
  defp find_label(bdd) do
    case bdd do
      true -> nil
      false -> nil
      {{_tag, fields}, _, _} when map_size(fields) > 0 -> {:label, Map.keys(fields) |> hd()}
      {_, left_bdd, right_bdd} -> find_label(left_bdd) || find_label(right_bdd)
    end
  end

  def empty_cases(bdd) do
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

  def map_split_on_label(d, label) do
    bdd_get(d)
    |> Enum.flat_map(fn {pos, neg} -> aux_p(pos, neg, label, []) end)
    |> pair_simplify_dnf(@term_or_undef)
  end

  # Splits a map literal on a label, returns a pair `{label_type, rest_of_map}`
  # where `rest_of_map` is obtained by removing `label`
  defp single_split({tag, fields}, label) do
    {label_type, rest_of_map} = Map.pop(fields, label)

    cond do
      label_type != nil -> {label_type, map_make(tag, rest_of_map)}
      tag == :closed -> {@undef, map_make(tag, rest_of_map)}
      # case where there is an open map with no labels { .. }
      map_size(fields) == 0 -> :no_split
      true -> {@term_or_undef, map_make(tag, rest_of_map)}
    end
  end

  def aux_p([], negative, label, pos_acc), do: aux_n(negative, label, pos_acc, [])

  def aux_p([map_literal | positive], negative, label, pos_acc) do
    case single_split(map_literal, label) do
      # { .. } the open map in a positive intersection can be ignored
      :no_split ->
        aux_p(positive, negative, label, pos_acc)

      # {typeof l, rest} is added to the positive accumulator
      {label_type, rest_of_map} ->
        aux_p(positive, negative, label, [{label_type, rest_of_map} | pos_acc])
    end
  end

  # same as aux_p, but for negative literals
  defp aux_n([], _, pos_acc, neg_acc), do: [{pos_acc, neg_acc}]

  defp aux_n([map_literal | negative], label, pos_acc, neg_acc) do
    case single_split(map_literal, label) do
      # { .. } in a negative intersection discards the entire {pos, neg} intersection
      :no_split ->
        []

      # {typeof l, rest} is added to the negative accumulator
      {label_type, rest_of_map} ->
        aux_n(negative, label, pos_acc, [{label_type, rest_of_map} | neg_acc])
    end
  end

  def map_to_quoted(bdd) do
    map_get_dnf(bdd)
    |> case do
      [] ->
        []

      x ->
        Enum.map(x, &map_dnf_to_quoted/1)
        |> Enum.reduce(&{:or, [], [&2, &1]})
        |> List.wrap()
    end
  end

  def map_dnf_to_quoted({:map_literal, [fields, is_open, has_empty]}) do
    case {is_open, has_empty} do
      {false, true} ->
        {:%{}, [], map_literal_to_quoted(fields, is_open)}

      {true, true} ->
        {:%{}, [], map_literal_to_quoted(fields, is_open) ++ [{:.., [], nil}]}

      {true, false} ->
        {:%{}, [],
         map_literal_to_quoted(fields, is_open) ++ [{:.., [], [{:+, [], [{:others, [], nil}]}]}]}
    end
  end

  def map_literal_to_quoted(map, is_open) do
    for {label, {optional_field?, type}} <- map,
        not (is_open and optional_field? and term?(type)) do
      if optional_field?,
        do: {{:optional, [], [label]}, to_quoted(type)},
        else: {label, to_quoted(type)}
    end
  end

  # BDD
  #
  # Generic BDD operations. Binary decision diagrams are binary trees used to
  # encode complex types.

  defp bdd_new(literal), do: {literal, true, false}

  defp bdd_union(true, _b), do: true
  defp bdd_union(_b, true), do: true
  defp bdd_union(false, b), do: b
  defp bdd_union(b, false), do: b

  defp bdd_union(b1 = {a1, c1, d1}, b2 = {a2, c2, d2}) do
    cond do
      a1 == a2 -> {a1, bdd_union(c1, c2), bdd_union(d1, d2)}
      a1 < a2 -> {a1, bdd_union(c1, b2), bdd_union(d1, b2)}
      a1 > a2 -> {a2, bdd_union(b1, c2), bdd_union(b1, d2)}
    end
  end

  defp bdd_intersection(false, _), do: false
  defp bdd_intersection(_, false), do: false
  defp bdd_intersection(true, b), do: b
  defp bdd_intersection(a, true), do: a

  defp bdd_intersection(bdd1 = {value1, high1, low1}, bdd2 = {value2, high2, low2}) do
    cond do
      value1 == value2 -> {value1, bdd_intersection(high1, high2), bdd_intersection(low1, low2)}
      value1 < value2 -> {value1, bdd_intersection(high1, bdd2), bdd_intersection(low1, bdd2)}
      value1 > value2 -> {value2, bdd_intersection(bdd1, high2), bdd_intersection(bdd1, low2)}
    end
  end

  defp bdd_difference(false, _), do: false
  defp bdd_difference(_, true), do: false
  defp bdd_difference(bdd, false), do: bdd

  defp bdd_difference(true, {value, high, low}) do
    {value, bdd_difference(true, high), bdd_difference(true, low)}
  end

  defp bdd_difference(bdd1 = {value1, high1, low1}, bdd2 = {value2, high2, low2}) do
    cond do
      value1 == value2 -> {value1, bdd_difference(high1, high2), bdd_difference(low1, low2)}
      value1 < value2 -> {value1, bdd_difference(high1, bdd2), bdd_difference(low1, bdd2)}
      value1 > value2 -> {value2, bdd_difference(bdd1, high2), bdd_difference(bdd1, low2)}
    end
  end

  def bdd_get(bdd), do: bdd_get(bdd, [], [])

  def bdd_get(false, _pos, _neg), do: []
  def bdd_get(true, pos_acc, neg_acc), do: [{pos_acc, neg_acc}]

  # TODO: optimize the ++
  def bdd_get({literal, bdd_left, bdd_right}, pos_acc, neg_acc) do
    bdd_get(bdd_left, [literal | pos_acc], neg_acc) ++
      bdd_get(bdd_right, pos_acc, [literal | neg_acc])
  end

  # Pair normalization

  def pair_simplify_dnf(dnf, term \\ @term) do
    Enum.flat_map(dnf, &pair_simplify_line([], &1, term))
  end

  def pair_simplify_line(accu, {positive, negative}, term \\ @term) do
    {fst, snd} = pair_intersection(positive, term)

    if empty?(fst) or empty?(snd) do
      accu
    else
      residual = none()

      {accu, residual} =
        make_pairs_disjoint(negative)
        |> Enum.reduce(
          {accu, residual},
          fn {t1, t2}, {accu, residual} ->
            i = intersection(fst, t1)
            j = intersection(snd, t2)

            if not_empty?(i) and not_empty?(j) do
              resid = union(residual, t1)
              snd_diff = difference(snd, t2)

              if not_empty?(snd_diff),
                do: {add_pair_to_disjoint_list(accu, i, snd_diff, []), resid},
                else: {accu, resid}
            else
              {accu, residual}
            end
          end
        )

      fst_diff = difference(fst, residual)

      if not_empty?(fst_diff),
        do: add_pair_to_disjoint_list(accu, fst_diff, snd, []),
        else: accu
    end
  end

  # Computes the component-wise intersection of a list of pairs.
  def pair_intersection(pair_list, term \\ @term) do
    Enum.reduce(pair_list, {term, term}, fn {x1, x2}, {acc1, acc2} ->
      {intersection(acc1, x1), intersection(acc2, x2)}
    end)
  end

  # Given the invariant that `disjoint_pairs ++ acc` forms a list of disjoint pairs,
  # the function goes through `disjoint_pairs` to see for which pairs `fst`
  # has a non-empty intersection with (overlap). The decomposition of `{fst, snd}`
  # over each such pair (at most three elements) gets added into `acc`.
  # In particular, if a pair is found such that `fst` is a subtype of the first
  # element, then there is no use to go through the whole list anymore (because
  # this pair was disjoint with the others).
  def add_pair_to_disjoint_list([], fst, snd, acc), do: [{fst, snd} | acc]

  def add_pair_to_disjoint_list([{s1, s2} | pairs], fst, snd, acc) do
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
          add_pair_to_disjoint_list(pairs, fst, union(snd, s2), acc)

        # if fst \ s1 = empty, then fst is a subtype of s1 and disjointness is ensured
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

  def make_pairs_disjoint(pairs) do
    Enum.reduce(pairs, [], fn {t1, t2}, acc -> add_pair_to_disjoint_list(acc, t1, t2, []) end)
  end
end
