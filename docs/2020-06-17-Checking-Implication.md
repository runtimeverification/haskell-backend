# Checking Implication

Checking implication is an important step for proving one-path and all-path reachability claims.
This document will describe logically how this step will be performed.

## Background

The reader should be familiar with the algorithm for proving one-path and all-path reachability claims:

- [One-Path](2018-11-08-One-Path-Reachability-Proofs.md)
- [All-Path](2019-03-28-All-Path-Reachability-Proofs.md)

## Problem

Consider a reachability claim,

```
φ(X) → ∘ ∃ Y. ψ(X, Y)
```

where `∘` denotes the appropriate one-path or all-path modality
and `X` and `Y` denote _distinct_ families of variables.
We will assume that `φ(X)` and `ψ(X, Y)` are function-like patterns (matching at most one value)
because this is true in typical use.

The reachability proof algorithm will unroll the modality, giving

```
φ(X) → ∃ Y. ψ(X, Y) ∨ • ∘ ∃ Y. ψ(X, Y)
```

If the direct implication holds,

```
φ(X) → ∃ Y. ψ(X, Y)
```

then the claim is proven.
Otherwise, the algorithm continues with

```
φ(X) → • ∘ ∃ Y. ψ(X, Y)
```

by rewriting `φ(X)`.
Here, were are concerned with checking the direct implication,

```
φ(X) → ∃ Y. ψ(X, Y)
```

or equivalently, checking that

```
φ(X) ∧ ¬ ∃ Y. ψ(X, Y)
```

is unsatisfiable.

## Solution

Checking that the formula

```
φ(X) ∧ ¬ ∃ Y. ψ(X, Y)
```

is unsatisfiable is equivalent to checking

```
⌈φ(X) ∧ ¬ ∃ Y. ψ(X, Y)⌉.
```

Because we assume that `φ(X)` is a function-like pattern,
we can move the negation outside of `⌈ ⌉`:

```
⌈φ(X) ∧ ¬ ∃ Y. ψ(X, Y)⌉
===
¬ ⌈φ(X) ∧ ∃ Y. ψ(X, Y)⌉ ∧ ⌈φ(X)⌉.
```

By alpha-equivalence, we can also move the quantifier outside of `⌈ ⌉`:

```
(¬ ⌈φ(X) ∧ ∃ Y. ψ(X, Y)⌉) ∧ ⌈φ(X)⌉
===
(¬ ∃ Y. ⌈φ(X) ∧ ψ(X, Y)⌉) ∧ ⌈φ(X)⌉.
```

## Optimization

We can optimize this solution in the typical case where

```
φ(X) = t₁(X) ∧ P₁(X)
ψ(X, Y) = t₂(X, Y) ∧ P₂(X, Y)
```

where `t₁(X)` and `t₂(X, Y)` are term-like patterns
and `P₁(X)` and `P₂(X, Y)` are predicates.
The unification of the left- and right-hand sides is

```
∃ Y. ⌈φ(X) ∧ ψ(X, Y)⌉
===
∃ Y. ⌈t₁(X) ∧ t₂(X, Y)⌉ ∧ P₁(X) ∧ P₂(X, Y)
===
P₁(X) ∧ ∃ Y. ⌈t₁(X) ∧ t₂(X, Y)⌉ ∧ P₂(X, Y)
```

so that

```
(¬ ∃ Y. ⌈φ(X) ∧ ψ(X, Y)⌉) ∧ ⌈φ(X)⌉
===
  ¬ P₁(X) ∧ ⌈φ(X)⌉
∨
  (¬ ∃ Y. ⌈t₁(X) ∧ t₂(X, Y)⌉ ∧ P₂(X, Y)) ∧ ⌈φ(X)⌉
```

The first term of the above disjuntion is `⊥`,

```
¬ P₁(X) ∧ ⌈φ(X)⌉
===
¬ P₁(X) ∧ ⌈t₁(X)⌉ ∧ P₁(X)
===
⊥
```

leaving only

```
(¬ ∃ Y. ⌈φ(X) ∧ ψ(X, Y)⌉)              ∧ ⌈φ(X)⌉
===
(¬ ∃ Y. ⌈t₁(X) ∧ t₂(X, Y)⌉ ∧ P₂(X, Y)) ∧ ⌈t₁(X)⌉ ∧ P₁(X).
```

The sub-term `⌈t₁(X) ∧ t₂(X, Y)⌉` is a unification problem with an efficient internal implementation.
The unification problem should be solved first because

```
⌈t₁(X) ∧ t₂(X, Y)⌉ → ⌈t₁(X)⌉
```

so that if unification succeeds, there is no need to explicitly consider `⌈t₁(X)⌉`.
If unification fails, then the negative conjunct is `\top` so that the implication is satisified when `⌈t₁(X)⌉ ∧ P₁(X)` is unsatisfiable.
Now, the implication is checked in two cases:
after a configuration is rewritten (in which case the configuration may be rewritten again)
or after a configuration can no longer be rewritten (a remainder pattern).
In the case of a rewritten configuration, when unification fails, there is no need to check the rest of the implication pattern:
the condition `t₁(X) ∧ P₁(X)` itself implies the condition `⌈t₁(X)⌉ ∧ P₁(X)`.

## Summary

The algorithm follows:

Given the implication

```
φ(X) → ∃ Y. ψ(X, Y)
```

with

```
φ(X) = t₁(X) ∧ P₁(X)
ψ(X, Y) = t₂(X, Y) ∧ P₂(X, Y)
```

where `t₁(X)` and `t₂(X, Y)` are term-like patterns
and `P₁(X)` and `P₂(X, Y)` are predicates,

1. Solve the unification problem `⌈t₁(X) ∧ t₂(X, Y)⌉`.
2. If unification succeeds, evaluate
   `\not(∃ Y. ⌈t₁(X) ∧ t₂(X, Y)⌉ ∧ P₂(X, Y)) ∧ P₁(X)`.
   The implication is valid iff the predicate is unsatisfiable.
3. If unification fails,
   1. If `φ(X)` is a remainder pattern, evaluate
      `⌈t₁(X)⌉ ∧ P₁(X)`.
      The implication is valid iff the predicate is unsatisfiable.
   2. If `φ(X)` is a rewritten pattern, assume the implication is not valid.

Aside: If we checked `⌈t₁(X)⌉ ∧ P₁(X)` in both cases above, then we could infer that the configuration is defined, which would allow us to do subsequent rewriting without generating extra definedness conditions. The efficiency of this method merits investigation.
