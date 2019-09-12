Configuration Splitting Simplification
======================================

Summary
-------

```
φ(X) ∧ (¬ ∃ Z. α(Z)) =  φ(X) ∧ (¬ ∃ Z. ⌈φ(X) ∧ α(Z)⌉)
```

under the conditions that 
1. `φ(X) = φt(X) ∧ φp(X)` where `φp(X)` is a predicate,
   and `φt(X)` is a function-like term. It may or may not unify with `α(Z)`.
1. `α(Z) = αt(Z) ∧ αp(Z)` where `αt(Z)` is a functional term,
   composed out of constructor-like symbols and variables
   and `αp(Z)` is a predicate (so `α(Z)` is function-like).
   
### Implementation concerns

If `φt(X)` and `αt(Z)` don't unify then 

```
φ(X) ∧ (¬ ∃ Z. α(Z)) = φ(X)
```

If `φt(X)` and `αt(Z)` unify with substitution `θ` binding all variables from `Z`
and with the unification predicate `θp(X)`, then

```
φ(X) ∧ (¬ ∃ Z. α(Z)) = φ(X) ∧ ¬(θp(X) ∧ θ(αp(Z)))
```

Background
----------

### Functional and function-like patterns

See the `glossary.md` file for term definitions (e.g.
[functional](glossary.md#functional) and
[function-like](glossary.md#functionlike)).

If `t` is functional (or function-like) and `φ` is a predicate,
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


### Assumptions

1. There exist `φt(X)` and `φp(X)` such that

   - `φ(X)` is `φt(X) ∧ φp(X)`
   - `φt(X)` is a function-like term
   - `φp(X)` is a predicate

1. `Z`, `t(Z)` and `p(Z)` such that

   - `α(Z) =  αt(Z) ∧ αp(Z)`
   - `αt(Z)` is a functional term made of constructor-like symbols and variables
   - `αp(Z)` is a predicate

__Note:__ The proposed solution should not return a broken result when these
assumptions do not hold, but it is not forced to fully simplify the given term.

### Justification

```
φ(X) ∧ (¬ ∃ Z. α(Z))
    =  φt(X) ∧ φp(X) ∧ (¬ ∃ Z. α(Z))
    =  φt(X) ∧ φp(X) ∧ ⌈φt(X) ∧ (¬ ∃ Z. α(Z))⌉ -- since φt(x) is function-like
    =  φ(X) ∧ ⌈φt(X) ∧ (∀ Z. ¬α(Z))⌉  -- ¬ ∃ = ∀ ¬
    =  φ(X) ∧ ⌈∀ Z. (φt(X) ∧ ¬α(Z))⌉  -- since φt(x) does not depend on Z
    =  φ(X) ∧ (∀ Z. ⌈φt(X) ∧ ¬α(Z)⌉)  -- ⌈∀⌉ = ∀⌈⌉
    =  ∀ Z. φ(X) ∧ ⌈φt(X) ∧ ¬α(Z)⌉  -- FOL
    =  ∀ Z. φ(X) ∧ ⌈φt(X) ∧ ¬(αt(Z) ∧ αp(Z))⌉ 
    =  ∀ Z. φ(X) ∧ ⌈φt(X) ∧ (¬αt(Z) ∨ ¬αp(Z))⌉ 
    =  ∀ Z. φ(X) ∧ ⌈(φt(X) ∧ ¬αt(Z)) ∨ (φt(X) ∧ ¬αp(Z))⌉ 
    =  ∀ Z. φ(X) ∧ (⌈φt(X) ∧ ¬αt(Z)⌉ ∨ ⌈φt(X) ∧ ¬αp(Z)⌉)
    =  ∀ Z. (φ(X) ∧ ⌈φt(X) ∧ ¬αt(Z)⌉) ∨ (φ(X) ∧ ⌈φt(X) ∧ ¬αp(Z)⌉)
    =  ∀ Z. (φ(X) ∧ ⌈φt(X) ∧ ¬αt(Z)⌉) ∨ (φt(X) ∧ φp(X) ∧ ⌈φt(X)⌉ ∧ ¬αp(Z))
    =  ∀ Z. (φ(X) ∧ ⌈φt(X) ∧ ¬αt(Z)⌉) ∨ (φ(X) ∧ ¬αp(Z))
    (1)
```

Note that, since `φt(X)` and `αt(Z)` is function-like, it is
easy to check semantically that:

```
⌈φt(X) ∧ ¬αt(Z)⌉ = ⌈φt(X)⌉ ∧ ¬⌈φt(X) ∧ αt(Z)⌉ (2)
```

So then we have
```
φ(X) ∧ (¬ ∃ Z. α(Z))
    =  ∀ Z. (φ(X) ∧ ⌈φt(X) ∧ ¬αt(Z)⌉) ∨ (φ(X) ∧ ¬αp(Z))   -- as per (1)
    =  ∀ Z. (φt(X) ∧ φp(X) ∧ ⌈φt(X)⌉ ∧ ¬⌈φt(X) ∧ αt(Z)⌉) ∨ (φ(X) ∧ ¬αp(Z)) -- from (2)
    =  ∀ Z. (φ(X) ∧ ¬⌈φt(X) ∧ αt(Z)⌉) ∨ (φ(X) ∧ ¬αp(Z))
    =  ∀ Z. (φ(X) ∧ ¬⌈φt(X) ∧ αt(Z)⌉) ∨ (φ(X) ∧ ¬αp(Z)) ∨ (φt(X) ∧ φp(X) ∧ ¬φp(X))
    =  ∀ Z. φ(X) ∧ (¬⌈φt(X) ∧ αt(Z)⌉ ∨ ¬αp(Z) ∨ ¬φp(X))
    =  ∀ Z. φ(X) ∧ ¬(⌈φt(X) ∧ αt(Z)⌉ ∧ αp(Z) ∧ φp(X))
    =  ∀ Z. φ(X) ∧ ¬⌈φt(X) ∧ αt(Z) ∧ αp(Z) ∧ φp(X)⌉
    =  ∀ Z. φ(X) ∧ ¬⌈φ(X) ∧ α(Z)⌉
    =  φ(X) ∧ (∀ Z. ¬⌈φ(X) ∧ α(Z)⌉)
    =  φ(X) ∧ (¬ ∃ Z. ⌈φ(X) ∧ α(Z)⌉)
```

### Implementation concerns

We have shown above that

```
φ(X) ∧ (¬ ∃ Z. α(Z))
    =  φ(X) ∧ (¬ ∃ Z. ⌈φt(X) ∧ αt(Z) ∧ φp(X) ∧ αp(Z)⌉)
    =  φ(X) ∧ (¬ ∃ Z. (⌈φt(X) ∧ αt(Z)⌉ ∧ φp(X) ∧ αp(Z)))
```

Now we need to do a case analysis on whether `φt(X)` and `αt(Z)` are unifiable.
If they are not, then `⌈φt(X) ∧ αt(Z)⌉` is `⊥`, hence 

```
φ(X) ∧ (¬ ∃ Z. (⌈φt(X) ∧ αt(Z)⌉ ∧ φp(X) ∧ αp(Z))) = φ(X)
```

If `φt(X)` and `αt(Z)` unify with substitution `θ` binding all variables from `Z`
and with the unification predicate `θp(X)`, then we can apply the substitution
and remove the quantification, obtaining

```
φ(X) ∧ (¬ ∃ Z. α(Z))
    =  φ(X) ∧ (¬ ∃ Z. (⌈φt(X) ∧ αt(Z)⌉ ∧ φp(X) ∧ αp(Z)))
    =  φ(X) ∧ ¬ (θp(X) ∧ φp(X) ∧ θ(αp(Z)) ∧ (∃ Z. θ))
    =  φ(X) ∧ ¬ (θp(X) ∧ φp(X) ∧ θ(αp(Z)))
    =  φ(X) ∧ (¬ (θp(X) ∧ θ(αp(Z))) ∨ ¬ φp(X))
    =  (φ(X) ∧ ¬ (θp(X) ∧ θ(αp(Z))) ∨ (φ(X) ∧ ¬ φp(X))
    =  (φ(X) ∧ ¬ (θp(X) ∧ θ(αp(Z)))) ∨ (φt(X) ∧ φp(X) ∧ ¬ φp(X))
    =  φ(X) ∧ ¬ (θp(X) ∧ θ(αp(Z)))
```
