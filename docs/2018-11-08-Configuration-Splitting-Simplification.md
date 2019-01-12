Configuration Splitting Simplification
======================================

Background
----------

### Functional and function-like patterns

A functional pattern has exactly one element, i.e. `t` is functional iff
`∃x . x=t`. A function-like pattern is similar, but it can also be `⊥`, i.e.
`t` is function-like if `(∃x . x=t) ∨ ⌈¬t⌉`.

Note that if `t` is functional (or function-like) and `φ` is a predicate,
then `t ∧ φ` is function-like.

In the sequel all of our pattern meta-variables will be assumes to denote
function-like patterns unless otherwise stated.

### Obtaining And-Not-Exists patterns from unrolling eventually.

As documented in [One path reachability proofs](2018-11-08-One-Path-Reachability-Proofs.md),
```
∀ X . φ(X) → ◆ ∃ Y . ψ(X, Y)
```
where `φ` and `ψ` are function-like patterns, is equivalent to proving
```
∀ X . φ(X) →  ∃ Y . ψ(X, Y) ∨ •◆ ∃ Y . ψ(X, Y)`
```

We can now move `∃ Y . ψ(X, Y)` to the left of the implication,
and (assuming law of excluded middle) we obtain the equivalent:
```
∀ X . φ(X) ∧ ¬∃ Y . ψ(X, Y) →  •◆ ∃ Y . ψ(X, Y)`
```

### Obtaining And-Not-Exists patterns from applying one step

When doing one-path reachability proofs and applying an axiom,
`∀ Z . α(Z) → •β(Z)`, where `•` is the strong-next symbol (aka 'next'),
to the following reachability goal
```
∀ X . Φ(X) → •◆ ∃ Y . ψ(X, Y)
```
the result will look something like
```
(∀ X . Φ'(X) → ◆ ∃ Y . ψ(X, Y))
∧
(∀ X . Φ(X) ∧ (¬ ∃ Z. α(Z)) → •◆ ∃ Y . ψ(X, Y))
```

Problem
-------

We want to rewrite `φ(X) ∧ (¬ ∃ Z. α(Z))` part of the pattern above
to something more manageable, preferably something that does not use `not`
and `exists`, except in cases where it can be handled by an SMT solver.

We will assume it is provable that
1. `φ(X) = t(X) ∧ p(X)` where `p(X)` is a predicate,
   and `t(X)` is a function-like term. It may or may not unify with `α(Z)`.
1. `α(Z) =  s(Z) ∧ q(Z)` where `s(Z)` is a functional term,
   composed out of constructor-like symbols and variables
   and `q(x)` is a predicate (so `α(Z)` is function-like).

The proposed solution should not return a broken result when these assumptions
do not hold, but it is not forced to fully simplify the given term.

Algorithm
---------

Input:

1. `t(X)` and `p(X)` such that

   - `φ(X)` is `t(X) ∧ p(X)`
   - `t(X)` is a function-like term
   - `p(X)` is a predicate

1. `Z`, `s(Z)` and `q(Z)` such that

   - `α(Z) =  s(Z) ∧ q(Z)`
   - `s(Z)` is a functional term made of constructor-like symbols and variables
   - `q(Z)` is a predicate


Output: `t'(X)` and `p'(X)` such that

   - `φ(X) ∧ (¬ ∃ Z. α(Z)) = t'(X) ∧ p'(X)` is provable
   - `t(X)` is a function-like term
   - `p(X)` is a predicate


```
φ(X) ∧ (¬ ∃ Z. α(Z)) =  t(X) ∧ p(X) ∧ (¬ ∃ Z. α(Z))
```
We will examine only the `t(X) ∧ (¬ ∃ Z. α(Z))` term next.
```
t(X) ∧ (¬ ∃ Z. α(Z))
    =  t(X) ∧ ⌈t(X) ∧ (¬ ∃ Z. α(Z))⌉ -- since t(x) is function-like
    =  t(X) ∧ ⌈t(X) ∧ (∀ Z. ¬α(Z))⌉  -- ¬ ∃ = ∀ ¬
    =  t(X) ∧ ⌈∀ Z. (t(X) ∧ ¬α(Z))⌉  -- since t(x) does not depend on Z
    =  t(X) ∧ (∀ Z. ⌈t(X) ∧ ¬α(Z)⌉)  -- ⌈∀⌉ = ∀⌈⌉
    (1)
```

We will try to simplify `⌈t(X) ∧ ¬α(Z)⌉`.
First, let us note that, if `t(X)` and `α(Z)` are functional, then
```
⌈t(X) ∧ ¬α(Z)⌉
    =  ¬(t(X) = α(Z))  -- easily checked semantically
    =  ¬⌈t(X) ∧ α(Z)⌉  -- for functional patterns, `∧` means equality.
    (2)
```

If `t(X)` is `⊥`, then `⌈t(X) ∧ ¬α(Z)⌉ = ⊥`, while `¬⌈t(X) ∧ α(Z)⌉ = ⊤`, so if
we write it as `⌈t(X) ∧ ¬α(Z)⌉ =  ⌈t(X)⌉ ∧ ¬⌈t(X) ∧ α(Z)⌉` we should also catch
that case.

So then we have
```
⌈t(X) ∧ ¬α(Z)⌉
    = ¬⌈t(X) ∧ α(Z)⌉           -- as mentioned above (2)
    = ⌈t(X)⌉ ∧ ¬⌈t(X) ∧ α(Z)⌉  -- since ⌈t(X) ∧ ¬α(Z)⌉ = ⌈t(X)⌉ ∧ ⌈t(X) ∧ ¬α(Z)⌉
    (3)
```

If `α(Z)` is `⊥`, then `⌈t(X) ∧ ¬α(Z)⌉ = ⌈t(X)⌉`,
and `⌈t(X)⌉ ∧ ¬⌈t(X) ∧ α(Z)⌉ = ⌈t(X)⌉`, which is fine.

So then we have
```
t(X) ∧ (¬ ∃ Z. α(Z))
    = t(X) ∧ (∀ Z. ⌈t(X) ∧ ¬α(Z)⌉)  -- as mentioned above (1)
    = t(X) ∧ (∀ Z. ⌈t(X)⌉ ∧ ¬⌈t(X) ∧ α(Z)⌉)  -- using (3)
    = t(X) ∧ ⌈t(X)⌉ ∧ (∀ Z. ¬⌈t(X) ∧ α(Z)⌉)  -- t(X) does not depend on Z
    = t(X) ∧ (∀ Z. ¬⌈t(X) ∧ α(Z)⌉)           -- kind of obvious
    = t(X) ∧ (¬∃Z . ⌈t(X) ∧ α(Z)⌉)           -- ¬ ∃ = ∀ ¬
    = t(X) ∧ (¬∃Z . ⌈t(X) ∧ s(Z) ∧ q(Z)⌉)    -- expanding α
    = t(X) ∧ (¬∃Z . (⌈t(X) ∧ s(Z)⌉ ∧ q(Z)))  -- q is a predicate
```

Now we need to do a case analysis on whether `t(X)` and `s(X)` are unifiable.
If they are not, then `⌈t(X) ∧ s(Z)⌉` is `⊥`,
hence `t(X) ∧ (¬ ∃ Z. α(Z)) = t(X)`, leading to:
```
φ(X) ∧ (¬ ∃ Z. α(Z)) = φ(X)
```
If they are then, assuming that we managed to substitute all `Z` variables,
and if `u(X)` is the predicate from the substitution together with `q`
(not depending on `Z` anymore, then
`∃Z . ⌈t(X) ∧ s(Z)⌉ ∧ q(Z) = u(X)`, so `t(X) ∧ (¬ ∃ Z. α(Z)) = t(X) ∧ ¬u(X)`,
leading to:
```
φ(X) ∧ (¬ ∃ Z. α(Z)) = φ(X) ∧ ¬u(X)
```
