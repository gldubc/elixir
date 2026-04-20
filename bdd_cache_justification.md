# BDD Cache Justification

This branch uses plain BDD operations for container types. That means the
performance of type checking now depends on standard BDD engineering concerns:

1. uniqueing equivalent nodes
2. memoizing repeated apply/simplify subproblems
3. keeping a stable literal order

The cache is not adding semantic shortcuts. It only avoids recomputing the same
syntactic BDD results.

## Why the cache is necessary

Two cases were measured directly with the current compiler changes:

- `AbsintheFederation`
- `Spitfire`

With the current cached implementation, `perf.py --tc-table` reports:

```text
| Codebase | TC Time |
|---|---:|
| Spitfire | 1.149 s |
| AbsintheFederation | 0.021 s |
```

With the BDD caches disabled but the same BDD ordering logic left in place:

```text
| Codebase | TC Time |
|---|---:|
| Spitfire | 13.908 s |
| AbsintheFederation | 0.165 s |
```

Regression without caches:

- `Spitfire`: `1.149s -> 13.908s` (`+12.759s`, about `12.1x`)
- `AbsintheFederation`: `0.021s -> 0.165s` (`+0.144s`, about `7.9x`)

The practical consequence is:

- `AbsintheFederation` still stays under 2 seconds without caches.
- `Spitfire` does not. It jumps to roughly 14 seconds.

## What is being cached

There are three distinct caches.

### 1. Unique table for BDD leaves and nodes

Equivalent leaves/nodes should be shared instead of rebuilt as duplicate terms.
Without this, the same tail can be reconstructed many times and memory/term size
grow quickly.

This is standard BDD hash-consing.

### 2. Apply cache for commutative BDD operations

This memoizes repeated subproblems for:

- `bdd_union/2`
- `bdd_intersection/2`

Once the recursion starts splitting large BDDs, the same pairs of sub-BDDs are
encountered repeatedly. Without an apply cache, the engine resolves those pairs
again and again.

This turned out to be the main missing piece for `Spitfire`.

### 3. Simplify cache for `bdd_simplify/2`

`bdd_split/4` repeatedly simplifies the same BDD under the same assumption set.
Memoizing those calls avoids re-running the same recursive pruning work.

## Why scope matters

There is an important distinction between:

- having the right cache tables
- giving those tables a wide enough lifetime

An initial explicit-threading rewrite was enough to remove `Process.get/put`
from the BDD engine and keep the compiler building, but it kept the cache only
for individual BDD operations.

Measured with that narrower scope:

```text
| Codebase | TC Time |
|---|---:|
| Spitfire | 30.119 s |
| AbsintheFederation | 0.292 s |
```

So the tables alone are not sufficient. Recreating them at every public BDD
entrypoint loses too much reuse, especially for `Spitfire`.

This is why the intended scope is broader: the cache has to live across a whole
top-level `Descr` operation, not just one `bdd_union/2` or `bdd_intersection/2`
call.

## Why this is the right cache

The target cache is:

- local to a single top-level type operation
- purely syntactic
- discardable after the operation completes

It is not:

- a global compiler cache
- persisted across modules
- dependent on semantic map reasoning

So the correct model is an ephemeral per-operation BDD work cache.

## Why the current `Process` storage is only a prototype

The current branch uses `Process.get/put` because it was the quickest way to
prove the algorithmic shape and validate the measurements.

That storage choice is not fundamental to the fix.

The intended compiler-quality version is:

- keep the public `Descr` API unchanged
- create a fresh ephemeral BDD cache at the start of `union/2`,
  `intersection/2`, `difference/2`, and `negation/1`
- thread that cache explicitly through internal `Descr` BDD functions

The current in-progress rewrite has completed the explicit cache threading
inside the BDD core itself. The remaining step is to widen the cache lifetime
to those top-level `Descr` operations so the performance matches the prototype.

In other words, the important part is the existence of the unique/apply/simplify
tables, not the use of the process dictionary to hold them.
