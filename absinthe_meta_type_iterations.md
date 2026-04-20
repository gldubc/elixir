# Absinthe Federation `meta` Type Iterations

This note records the growth pattern seen while typechecking:

```elixir
Absinthe.Federation.Schema.Phase.AddFederatedDirectives.maybe_add_directives/2
```

The source variable is `meta`. The checker variable named `domain` is different:
it is the inferred argument-domain list for the callee, for example:

```elixir
domain = [expected_type_for_node, expected_type_for_meta]
```

At each local call in the pipe, the checker does roughly:

```elixir
meta_next = compatible_intersection(meta_previous, expected_type_for_meta)
```

The refining path is:

```text
Module.Types.Apply.local/7
  -> local_domain/6 computes the callee argument domain
  -> zip_map_reduce(args, domain, ...) checks each argument against its expected type
  -> Expr.of_expr(meta, expected_type_for_meta, ...)
  -> Of.refine_body_var(...)
  -> compatible_intersection(old_meta_type, expected_type_for_meta)
```

## Simplified Notation

Let:

```text
A_ok  = map has :absinthe_adapter and its value is atom()
A_bad = map has :absinthe_adapter and its value is not atom()
K     = map has :key_fields with a value that selects a directive-building clause
E     = map has :external == true
R     = map has :requires_fields
P     = map has :provides_fields
X     = map has :extends == true
S     = map has :shareable == true
O     = map has :override_from
```

Most helpers have the shape:

```elixir
defp maybe_add_foo_directive(node, %{foo: value, absinthe_adapter: adapter}) do
  Directive.build(..., adapter, ...)
  ...
end

defp maybe_add_foo_directive(node, _meta), do: node
```

Because `Directive.build/3` requires `adapter` to be an atom, the inferred safe
domain for the second argument is approximately:

```text
not (A_bad and Foo)
```

So each helper adds one more condition:

```text
T0 = term()
T1 = T0 and not (A_bad and K)
T2 = T1 and not (A_bad and E)
T3 = T2 and not (A_bad and R)
T4 = T3 and not (A_bad and P)
...
```

Factored logically, this is compact:

```text
not A_bad or (not K and not E and not R and not P and ...)
```

The descriptor representation does not keep it factored that way. It partitions
the map space by each independent key condition, so every new helper can split
the existing map partitions again.

## First Rendered Domain

The first helper, `maybe_add_key_directive/2`, produces this expected type for
the `meta` argument:

```text
%{..., absinthe_adapter: atom(), key_fields: binary()} or
  %{..., absinthe_adapter: term(), key_fields: empty_list() or non_empty_list(term(), term())} or
  (map() and
     not (%{..., absinthe_adapter: term(), key_fields: binary()} or
            %{
              ...,
              absinthe_adapter: term(),
              key_fields: empty_list() or non_empty_list(term(), term())
            })) or atom() or bitstring() or empty_list() or float() or fun() or integer() or
  non_empty_list(term(), term()) or pid() or port() or reference() or {...}
```

That type is close to `term()`, but not equal to `term()`: it excludes the region
where the key-directive clause would match and then call `Directive.build/3` with
a non-atom adapter.

## Measured Iterations

These are the measured descriptor sizes for the source variable `meta` after the
checker refines it against each helper's second-argument domain:

| Step | Pipe call | New condition, simplified | `meta` descriptor words |
| ---: | --- | --- | ---: |
| 0 | before pipe | `T0 = term()` / dynamic upper bound | small |
| 1 | `maybe_add_key_directive(meta)` | `T1 = T0 and not (A_bad and K)` | 153 |
| 2 | `maybe_add_external_directive(meta)` | `T2 = T1 and not (A_bad and E)` | 235 |
| 3 | `maybe_add_requires_directive(meta)` | `T3 = T2 and not (A_bad and R)` | 338 |
| 4 | `maybe_add_provides_directive(meta)` | `T4 = T3 and not (A_bad and P)` | 543 |
| 5 | `maybe_add_extends_directive(meta)` | `T5 = T4 and not (A_bad and X)` | 1,013 |
| 6 | `maybe_add_shareable_directive(meta)` | `T6 = T5 and not (A_bad and S)` | 2,023 |
| 7 | `maybe_add_override_directive(meta)` | `T7 = T6 and not (A_bad and O)` | 4,280 |
| 8 | `maybe_add_inaccessible_directive(meta)` | adds another independent map-key condition | 9,346 |

The full run continued:

```text
20,580
45,193
98,990
215,872
468,005
1,008,726
2,164,219
```

By the time the checker reaches `maybe_add_cost_directive/2`, it is not checking
a complicated source function. It is applying a small two-clause function to a
very large accumulated type for the unchanged source variable `meta`.

## Why It Grows

Each helper's inferred domain is small on its own. The growth comes from
repeatedly refining the same source variable with independent map conditions.

The semantic shape is:

```text
if `meta` has a directive key that selects a directive-building clause,
then `meta.absinthe_adapter` must be an atom.
```

After many helpers, this becomes:

```text
if `meta` has any of these directive keys in the matching shape,
then `meta.absinthe_adapter` must be an atom.
```

That can be stated compactly, but the current descriptor operations keep the
per-key partitions instead of widening or factoring them. That is the source of
the blow-up.

## Why Path Uniqueness Does Not Save This

The important correction is that the blow-up does not require the same map
literal to repeat along one path. The paths can be unique and still grow
exponentially.

For example, the first helper's domain is not stored directly as:

```text
not (A_bad and key_fields_is_binary)
```

It is stored closer to:

```text
good_key_case or (map() and not key_pattern_case) or non_map()
```

where:

```text
good_key_case    = %{..., absinthe_adapter: atom(), key_fields: binary()}
key_pattern_case = %{..., absinthe_adapter: term(), key_fields: binary()}
```

Semantically, `good_key_case` is a subtype of `key_pattern_case`. Therefore
this part could be compacted to:

```text
map() and not %{..., absinthe_adapter: not atom(), key_fields: binary()}
```

With only plain BDD operations, that semantic map relationship is not used.
The two map literals are treated like distinct ordered BDD variables. The BDD
can enforce "do not put the same variable twice on a path", but it does not know:

```text
good_key_case and not key_pattern_case = empty
good_key_case or (map() and not key_pattern_case)
  = map() and not (key_pattern_case and not good_key_case)
```

The next helper adds the same shape for another key:

```text
good_external_case or (map() and not external_pattern_case) or non_map()
```

Intersecting those two domains distributes the alternatives:

```text
(good_key or not key_pattern) and (good_external or not external_pattern)
```

which gives paths for:

```text
good_key and good_external
good_key and not external_pattern
not key_pattern and good_external
not key_pattern and not external_pattern
```

Many of these are semantically reducible or impossible once map-literal subtype
and overlap are considered. Plain BDD operations only see different literals, so
they keep the cross-product. After N directive helpers, path uniqueness still
allows roughly one path per combination of the N helper alternatives.

The simplifiers currently visible in `bdd_split/4` and `bdd_simplify/2` prune
exact BDD equality/coverage and exact repeated assumptions. They do not perform
map-literal implication, map-literal disjointness, or map-literal difference.
So the BDD is structurally normalized, but it is not semantically minimized for
overlapping map literals.

## Path Uniqueness Verification

I added a syntactic BDD verifier and ran Absinthe with:

```sh
BDD_VERIFY_ABSINTHE=1 ba
```

The verifier checks:

- stored BDD node hashes match the literal/branch contents
- every descendant BDD head is strictly greater than its ancestor literal in
  the BDD literal order
- the check is applied recursively to nested map/list/tuple/function BDDs inside
  the descriptor

So this verifies path uniqueness/order, not semantic map disjointness or subtype
relationships.

The exploding Absinthe `meta` type passed this invariant at each pipe step:

| Pipe call | Words | BDD terms visited | Nodes | Leaves | Max depth |
| --- | ---: | ---: | ---: | ---: | ---: |
| `maybe_add_key_directive/2:28` | 153 | 17 | 4 | 5 | 4 |
| `maybe_add_external_directive/2:29` | 235 | 34 | 9 | 10 | 6 |
| `maybe_add_requires_directive/2:30` | 338 | 67 | 20 | 16 | 8 |
| `maybe_add_provides_directive/2:31` | 543 | 151 | 48 | 28 | 10 |
| `maybe_add_extends_directive/2:32` | 1,013 | 365 | 118 | 56 | 12 |
| `maybe_add_shareable_directive/2:33` | 2,023 | 845 | 278 | 104 | 14 |
| `maybe_add_override_directive/2:34` | 4,280 | 2,045 | 646 | 296 | 16 |
| `maybe_add_inaccessible_directive/2:35` | 9,346 | 4,657 | 1,482 | 592 | 18 |
| `maybe_add_interface_object_directive/2:36` | 20,580 | 10,457 | 3,346 | 1,184 | 20 |
| `maybe_add_requires_scopes_directive/2:37` | 45,193 | 23,129 | 7,442 | 2,336 | 22 |
| `maybe_add_policy_directive/2:38` | 98,990 | 50,777 | 16,402 | 4,640 | 24 |
| `maybe_add_authenticated_directive/2:39` | 215,872 | 110,761 | 35,874 | 9,280 | 26 |
| `maybe_add_context_directive/2:40` | 468,005 | 239,945 | 77,890 | 18,560 | 28 |
| `maybe_add_list_size_directive/2:41` | 1,008,726 | 528,713 | 168,002 | 49,280 | 30 |
| `maybe_add_cost_directive/2:42` | 2,164,219 | 1,131,145 | 360,578 | 98,560 | 32 |

The ordering is strictly increasing from root to descendants. The growth is
therefore not caused by a broken BDD path-order invariant in this reproducer.

## Structural Fix

The failure mode turned out to be syntactic BDD variable ordering plus missing
DAG sharing.

With the original Erlang term order, map literals were ordered primarily by the
first field key. In this reproducer that first key is the shared
`:absinthe_adapter` field. That separates the related literals produced by each
directive helper and makes the BDD enumerate subsets of helpers.

After changing BDD map-literal ordering to compare map fields in reverse key
order, the directive-specific fields come before the shared adapter field and
the unique BDD node count becomes linear:

```text
maybe_add_cost_directive/2:42
unique_nodes=32
unique_leaves=3
max_depth=32
```

The remaining large word count was duplicated copies of those same nodes. Adding
structural hash-consing for BDD leaves/nodes reduces the final exploding
`meta` type to:

```text
maybe_add_cost_directive/2:42
words=935
bdds=222592
nodes=73727
leaves=25986
unique_nodes=32
unique_leaves=3
max_depth=32
ok
```

The verifier still reports many visited nodes because it intentionally walks the
tree recursively without a seen set. The actual term size is now small because
the repeated tails are shared.

The plain Absinthe compile now reports:

```text
[profile] Finished group pass check of 22 modules in 186ms
```
