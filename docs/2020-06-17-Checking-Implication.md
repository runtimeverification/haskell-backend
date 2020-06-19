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
===
φ(X) ∧ ¬ ∃ Y. ψ(X, Y) → • ∘ ∃ Y. ψ(X, Y)
```

If the direct implication holds, then

```
φ(X) ∧ ¬ ∃ Y. ψ(X, Y)
```

is unsatisfiable.
Otherwise, the reachability proof algorithm continues by rewriting the configuration.

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
φ(X) = t(X) ∧ P(X)
ψ(X, Y) = ⋁ᵢ tᵢ(X, Y) ∧ Pᵢ(X, Y)
```

where `t(X)` and `tᵢ(X, Y)` are term-like patterns
and `P(X)` and `Pᵢ(X, Y)` are predicates.
The unification of the left- and right-hand sides is

```
∃ Y. ⌈φ(X) ∧ ψ(X, Y)⌉
===
⋁ᵢ ∃ Y. ⌈t(X) ∧ tᵢ(X, Y)⌉ ∧ P(X) ∧ Pᵢ(X, Y)
===
P(X) ∧ ⋁ᵢ ∃ Y. ⌈t(X) ∧ tᵢ(X, Y)⌉ ∧ Pᵢ(X, Y)
```

so that

```
(¬ ∃ Y. ⌈φ(X) ∧ ψ(X, Y)⌉) ∧ ⌈φ(X)⌉
===
  ¬ P(X) ∧ ⌈φ(X)⌉
∨
  (¬ ⋁ᵢ ∃ Y. ⌈t(X) ∧ tᵢ(X, Y)⌉ ∧ Pᵢ(X, Y)) ∧ ⌈φ(X)⌉
```

The first term of the above disjuntion is `⊥`,

```
¬ P(X) ∧ ⌈φ(X)⌉
===
¬ P(X) ∧ ⌈t(X)⌉ ∧ P(X)
===
⊥
```

leaving only

```
(¬    ∃ Y. ⌈φ(X) ∧ ψ(X, Y)⌉            ) ∧ ⌈φ(X)⌉
===
(¬ ⋁ᵢ ∃ Y. ⌈t(X) ∧ tᵢ(X, Y)⌉ ∧ Pᵢ(X, Y)) ∧ ⌈t(X)⌉ ∧ P(X).
===
(⋀ᵢ ¬ ∃ Y. ⌈t(X) ∧ tᵢ(X, Y)⌉ ∧ Pᵢ(X, Y)) ∧ ⌈t(X)⌉ ∧ P(X).
```

The sub-terms `⌈t(X) ∧ tᵢ(X, Y)⌉` are unification problems with an efficient internal implementation.
The unification problems should be solved first because

```
⌈t(X) ∧ tᵢ(X, Y)⌉ → ⌈t(X)⌉
```

so that if unification succeeds on any branch, there is no need to explicitly consider `⌈t(X)⌉`.
If unification fails, then the negative conjunct is `\top` so that the implication is satisified only when `⌈t(X)⌉ ∧ P(X)` is unsatisfiable.
Now, the implication is checked in two cases:
after a configuration is rewritten (in which case the configuration may be rewritten again)
or after a configuration can no longer be rewritten (a remainder pattern).
In the case of a rewritten configuration, when unification fails, there is no need to check the rest of the implication pattern:
the condition `t(X) ∧ P(X)` itself implies the condition `⌈t(X)⌉ ∧ P(X)`.

## Summary

The algorithm follows:

Given the implication

```
φ(X) → ∃ Y. ψ(X, Y)
```

with

```
φ(X) = t(X) ∧ P(X)
ψ(X, Y) = ⋁ᵢ tᵢ(X, Y) ∧ Pᵢ(X, Y)
```

where `t(X)` and `tᵢ(X, Y)` are term-like patterns
and `P(X)` and `Pᵢ(X, Y)` are predicates,

1. Solve the unification problems `⌈t(X) ∧ tᵢ(X, Y)⌉`.
2. If unification succeeds on any branch, evaluate
   `(⋀ᵢ ¬ ∃ Y. ⌈t(X) ∧ tᵢ(X, Y)⌉ ∧ Pᵢ(X, Y)) ∧ ⌈t(X)⌉ ∧ P(X)`.
   The implication is valid iff the predicate is unsatisfiable.
3. If unification fails on all branches,
   1. If `φ(X)` is a remainder pattern, evaluate
      `⌈t(X)⌉ ∧ P(X)`.
      The implication is valid iff the predicate is unsatisfiable.
   2. If `φ(X)` is a rewritten pattern, assume the implication is not valid.

Aside: If we checked `⌈t(X)⌉ ∧ P(X)` in both cases above, then we could infer that the configuration is defined, which would allow us to do subsequent rewriting without generating extra definedness conditions. The efficiency of this method merits investigation.
