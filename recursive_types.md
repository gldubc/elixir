# Recursive Types via Type Nodes in Elixir

### A coinductive representation using closures and maps

---

**Abstract.**
We describe a technique for representing recursive types in Elixir by introducing a *type node* structure. A type node pairs a *state*—a map recording one stepping step for every recursion variable—with a *generator function* that, given a state, produces a type descriptor (*descr*). This coinductive encoding naturally extends to mutually recursive definitions, keeps each node self-contained, and integrates smoothly with set-theoretic operations such as union.

---

## Table of Contents

1. [Background: Type Descriptors](#1-background-type-descriptors)
2. [Type Nodes](#2-type-nodes)
3. [The Role of Nodes and Descriptors](#3-the-role-of-nodes-and-descriptors)
4. [Constructing Recursive Types](#4-constructing-recursive-types)
5. [Example: Simple Recursive List](#5-example-simple-recursive-list)
6. [Example: Mutually Recursive Types](#6-example-mutually-recursive-types)
7. [Using Nodes in Set Operations](#7-using-nodes-in-set-operations)
8. [Node Identity and Memoization](#8-node-identity-and-memoization)
9. [Summary](#9-summary)
10. [Implementation Plan](#10-implementation-plan)

---

## 1. Background: Type Descriptors

A *type descriptor* (or simply *descr*) is an Elixir map whose keys are type-kind tags and whose values describe the inhabitants of that kind:

```
descr = %{atom => atom_kind, tuple => tuple_kind, ...}
```

For example, the type "integer or `nil`" is represented as:

```
%{integer => true, atom => [:nil]}
```

Here `integer => true` means "integers are present" (as a whole) and `atom => [:nil]` means "the atoms present are the set {`nil`}".

Descriptors support set-theoretic operations (union, intersection, negation) defined pointwise on each kind. We assume these operations are already implemented and focus on the extension to *recursive* types.

## 2. Type Nodes

**Definition 2.1 (Type node).** A *type node* is a triple

```
node = (id, state, f : state → descr)
```

where:

- **id** is a unique identity (an Elixir `reference()`, see [Section 8](#8-node-identity-and-memoization));
- **state** is a map `%{X => f_X, Y => f_Y, ...}` that records, for every recursion variable, its *generator function*; and
- **f** is one such generator function, producing a `descr` when applied to a state.

In Elixir syntax a node is simply a three-element tuple:

```elixir
{id, state, f}
```

**Definition 2.2 (stepping).** To *step* a node n_X = (id_X, state, f_X), we apply the generator to the state:

```
step(n_X) = f_X(state)
```

This yields a descriptor in which every occurrence of a recursion variable Y has been replaced by a fresh, self-contained node (id_Y, state, f_Y). stepping can therefore be iterated as many times as needed.

## 3. The Role of Nodes and Descriptors

It is important to distinguish two layers and the operations that belong to each.

**Descriptors are types.** A `descr` is the canonical representation of a type. All set-theoretic operations—union, intersection, negation, difference—are defined on descriptors and return descriptors:

```
union : descr × descr → descr
inter : descr × descr → descr
etc.
```

**Nodes are used by type constructors.** Type constructors—`tuple`, `map`, `list`, etc.—build composite types and take *nodes* as their arguments. For instance:

- `tuple([n_1, ..., n_k])` builds the tuple type {n_1, ..., n_k};
- `list(n)` builds the list type whose elements have type n;
- `map([{k_1, n_1}, ...])` builds a map type with the given key–value associations.

By accepting nodes rather than descriptors, constructors can refer to types that have not yet been fully expanded—which is exactly what is needed for recursive definitions.

**Descriptors pass as nodes.** Since a descriptor d can always be lifted to a node via `fresh_node(d) = (make_ref(), %{}, fn _ -> d end)`, descriptors can be used wherever a node is expected. In practice the implementation can accept both representations transparently.

**Constructors ≠ set operations.** Constructors and set operations live at different levels:

|                                              | **Inputs**        | **Output** |
|----------------------------------------------|-------------------|------------|
| Type constructors (`tuple`, `list`, ...)     | node, ..., node   | descr      |
| Set operations (`union`, `inter`, ...)       | descr, descr      | descr      |

Constructors consume nodes because they need to embed possibly-recursive sub-types into a descriptor. Set operations, on the other hand, combine already-formed descriptors pointwise by kind.

## 4. Constructing Recursive Types

The construction proceeds in four steps.

### Step 1 — Read the equations and build generator functions

For each recursive equation X = τ_X, we build a function f_X = `fn state -> d_X` where d_X is the body of the equation, translated into a descriptor, with every reference to a recursion variable Y replaced by the node expression `(make_ref(), state, state.Y)`.

### Step 2 — Collect all generators

This yields a family of generator functions f_X, f_Y, ..., one per equation.

### Step 3 — Build the state

Assemble the state map:

```
state = %{X => f_X, Y => f_Y, ...}
```

The state captures *all the ways to perform one stepping step* for each variable.

### Step 4 — Build the type nodes

Each recursive type is now represented as a node (with a fresh id):

```
n_X = (id_X, state, f_X)
n_Y = (id_Y, state, f_Y)
...
```

## 5. Example: Simple Recursive List

Consider the recursive type "list of integers":

```
X = {int, X} | nil
```

**Generator.**

```
f_X = fn state ->
  %{tuple => [:int, (make_ref(), state, state.X)],
    atom  => [:nil]}
end
```

**State.**

```
state = %{X => f_X}
```

**Node.**

```
n_X = (id_X, state, f_X)
```

In Elixir:

```elixir
fX = fn state ->
  %{tuple: [:int, {make_ref(), state, state[:X]}],
    atom: [:nil]}
end

state = %{X: fX}
nX = {make_ref(), state, fX}
```

stepping once:

```elixir
step(nX)
```

returns the descriptor:

```
%{tuple => [:int, (id', state, f_X)],
  atom  => [:nil]}
```

The inner `(id', state, f_X)` is itself a self-contained node that can be steped again at will.

## 6. Example: Mutually Recursive Types

```
Y = {bool, X} | nil
X = {int,  Y} | nil
```

**Step 1 — Generators.**

```
f_Y = fn state ->
  %{tuple => [:bool, (make_ref(), state, state.X)],
    atom  => [:nil]}
end

f_X = fn state ->
  %{tuple => [:int, (make_ref(), state, state.Y)],
    atom  => [:nil]}
end
```

**Step 3 — State.**

```
state = %{Y => f_Y, X => f_X}
```

**Step 4 — Nodes.**

```
n_Y = (id_Y, state, f_Y)
n_X = (id_X, state, f_X)
```

In Elixir:

```elixir
fY = fn st ->
  %{tuple: [:bool, {make_ref(), st, st[:X]}],
    atom: [:nil]}
end

fX = fn st ->
  %{tuple: [:int, {make_ref(), st, st[:Y]}],
    atom: [:nil]}
end

state = %{Y: fY, X: fX}

nY = {make_ref(), state, fY}
nX = {make_ref(), state, fX}
```

## 7. Using Nodes in Set Operations

Set-theoretic operations on descriptors (union, intersection, ...) are extended to nodes by first stepping each operand to obtain a descriptor and then computing the operation on descriptors.

### 7.1 Union of Two Nodes

Given two nodes n_1 = (id_1, state_1, f_1) and n_2 = (id_2, state_2, f_2), the union is computed as follows:

1. **step** both nodes: d_1 = f_1(state_1), d_2 = f_2(state_2).
2. **Compute** the pointwise union of the two descriptors: d = union_descr(d_1, d_2).
3. **Wrap** the result into a self-contained node using `fresh_node`: union_node(n_1, n_2) = fresh_node(union_descr(d_1, d_2)).

> **Remark (Self-containedness).** Each node produced by stepping is *self-contained*: the triple (id, state, f_Y) already carries enough information to be steped further without any external context. An alternative design would thread the state through every set operation, but self-containedness simplifies the interface: a node is a black box that can be steped on demand.

### 7.2 Conversion Functions

Two functions convert between nodes and descriptors:

```elixir
# node → descr
def step({_id, state, f}), do: f.(state)

# descr → node
def fresh_node(d) do
  {make_ref(), %{}, fn _state -> d end}
end
```

`step` takes a node and produces a descriptor by applying the generator to its state. `fresh_node` takes a descriptor and wraps it into a trivial node with a fresh id, an empty state, and a constant generator.

### 7.3 Elixir Sketch

```elixir
def union_node(n1, n2) do
  d1 = step(n1)
  d2 = step(n2)
  fresh_node(union_descr(d1, d2))
end
```

## 8. Node Identity and Memoization

So far a node is a pair (state, f). In practice we augment it with a unique *identity* tag, making a node a triple:

```
node = (id, state, f : state → descr)
```

In Elixir the identity is a fresh `reference()` obtained by calling `make_ref()`:

```elixir
def make_node(state, f) do
  {make_ref(), state, f}
end
```

References are unique values that support constant-time equality comparison. Two nodes created at different call sites will always have distinct identities, even if they happen to carry the same state and generator.

**Why an identity?** The emptiness decision algorithm for set-theoretic types [1] works by exploring nodes and memoizing which ones have already been visited. Without an identity, the algorithm would need structural comparison of closures—which is impossible in general. With a reference-based identity, the algorithm can record visited nodes in a `MapSet` keyed by their id, guaranteeing termination of the recursive exploration in the presence of cyclic types.

```elixir
def empty?(node, seen \\ MapSet.new())
def empty?({id, _state, _f} = node, seen) do
  if MapSet.member?(seen, id) do
    true
  else
    seen = MapSet.put(seen, id)
    descr = step(node)
    empty_descr?(descr, seen)
  end
end
```

The `seen` set acts as the memoization table: when a node is encountered a second time (detected via its id), the algorithm can conclude without re-exploring it—following the coinductive interpretation that a type variable encountered again is not empty (it contributes no new inhabitants but does not block either).

**Updated conversion functions.** With the triple representation, the conversion functions become:

```elixir
# node → descr
def step({_id, state, f}), do: f.(state)

# descr → node
def fresh_node(d) do
  {make_ref(), %{}, fn _state -> d end}
end
```

## 9. Summary

| **Concept**              | **Elixir representation**         |
|--------------------------|-----------------------------------|
| Type descriptor (descr)  | `%{atom: ..., tuple: ..., ...}`   |
| Generator function (f_X) | `fn state -> descr end`           |
| State (state)            | `%{X: fX, Y: fY, ...}`           |
| Type node (node)         | `{id, state, fX}`                 |
| Node identity            | `make_ref()`                      |
| stepping                | `fX.(state)`                      |

The key insight is that every recursive type is encoded as a pair of (i) a shared state recording one stepping step per variable and (ii) the particular generator for the variable of interest. This representation is *coinductive*: we never build an infinite object; instead, we lazily produce one layer of the type on demand by calling `f(state)`.

---

## 10. Implementation Plan

The following is an ordered list of implementation blocks. Within each block, all items must be implemented together (they are mutually dependent). Blocks themselves are listed in dependency order: a block can only be started once all blocks it depends on are complete.

### Block A — Core node module *(no dependencies)*

This block introduces the node data structure and the basic conversion functions. It touches no existing code.

- **A.1** Define the node triple `{id, state, f}`.
- **A.2** Implement `make_node(state, f)` which calls `make_ref()` to produce a fresh id.
- **A.3** Implement step : node → descr, i.e. `step({_id, state, f}) = f.(state)`.
- **A.4** Implement fresh_node : descr → node, i.e. `fresh_node(d) = {make_ref(), %{}, fn _ -> d end}`.
- **A.5** Implement a coercion helper `to_node(x)` that returns `x` unchanged if it is already a node, or calls `fresh_node(x)` if it is a descr. This allows callers to pass either representation transparently.

### Block B — Kind internals: descr → node *(depends on A)*

This is the largest and most invasive block. Every type kind (`tuple_kind`, `list_kind`, `map_kind`, ...) currently stores nested *descrs* for its sub-types. These must all change to store *nodes* instead.

- **B.1** Change the internal representation of each kind so that sub-type positions hold nodes rather than descrs. For example, `tuple_kind` for arity k stores k nodes instead of k descrs.
- **B.2** Update every type constructor (`tuple/1`, `list/1`, `map/1`, ...) to accept nodes as arguments (using `to_node` for backward compatibility).
- **B.3** Update all kind-level set operations (union, intersection, negation *per kind*) to handle nodes in sub-type positions. Where these operations need to combine sub-types, they must use the node-level operations from Block C (or operate structurally on nodes without stepping, depending on the algorithm).
- **B.4** Update every pattern match and traversal of kind internals across the codebase to expect nodes where descrs were before.

> **Remark.** Items B.1–B.4 are tightly coupled: changing the internal representation (B.1) immediately breaks all constructors (B.2), kind-level operations (B.3), and traversals (B.4). They must all be updated in a single atomic change.

### Block C — Set operations on nodes *(depends on A)*

These are thin wrappers: step both operands, apply the descr-level operation, wrap the result.

- **C.1** Implement `union_node(n1, n2)`.
- **C.2** Implement `inter_node(n1, n2)`.
- **C.3** Implement `negate_node(n)`.
- **C.4** Implement `diff_node(n1, n2)`.

Block C can be implemented in parallel with Block B (both depend only on A), but Block B.3 may call into Block C functions.

### Block D — Recursive type builder *(depends on A + B)*

The four-step construction algorithm from [Section 4](#4-constructing-recursive-types).

- **D.1** Read recursive type equations and produce generator functions f_X = `fn state -> d_X`.
- **D.2** Collect all generators into the state map state = `%{X => f_X, ...}`.

  %{X => f_X}
  f_X = fn state -> tuple([integer(), {state, state.X}]) |> union(atom(:nil)) end

- **D.3** Build each type node via `make_node(state, fX)`.
- **D.4** Integrate with the module/function that translates user-facing type syntax into the internal representation.

### Block E — Emptiness with memoization *(depends on A + B)*

- **E.1** Update `empty?/1` to accept nodes (not just descrs).
- **E.2** Add a `seen` parameter (`MapSet` of node ids) threaded through the recursion.
- **E.3** When a node id is already in `seen`, return `true` (coinductive base case).
- **E.4** Update `empty_descr?` so that when it recurses into kind sub-types (which are now nodes), it calls the node-level `empty?` with the `seen` set.

### Block F — Remaining recursive algorithms *(depends on A + B + E)*

Every algorithm that recurses into the sub-types of a descriptor must be updated in the same spirit as emptiness.

- **F.1** Subtyping: thread a memoization set; handle nodes in sub-type positions.
- **F.2** Pretty-printing / `to_string`: step nodes on demand and track visited ids to avoid infinite output.
- **F.3** Any other traversal (e.g. type normalization, materialization) that inspects kind internals.

### Dependency Graph

```
         ┌─────────────┐
         │ A: Core nodes│
         └──────┬──────┘
           ┌────┴────┐
           ▼         ▼
  ┌──────────────┐ ┌─────────────────┐
  │B: Kind       │ │C: Set ops on    │
  │   internals  │◄┤   nodes         │
  └──┬───┬───┬──┘ │ (B.3 may call C)│
     │   │   │    └─────────────────┘
     ▼   │   ▼
┌────────┐│┌──────────┐
│D: Rec. │││E:        │
│ builder│││ Emptiness│
└────────┘│└────┬─────┘
          │     │
          ▼     ▼
      ┌────────────┐
      │F: Other    │
      │  algorithms│
      └────────────┘
```

---

### References

[1] Mickaël Laurent and Kim Nguyen. *Implementing Set-Theoretic Types.* Proceedings of the ACM on Programming Languages, 8(POPL), 2024.