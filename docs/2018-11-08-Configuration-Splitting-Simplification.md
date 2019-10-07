Configuration Splitting Simplification
======================================

Summary
-------

If `φ(X)` and `α(Z)` are function-like formulae, then

```
φ(X) ∧ (¬ ∃ Z. α(Z)) = φ(X) ∧ (¬ ∃ Z. ⌈φ(X) ∧ α(Z)⌉)
```

### Implementation concerns

We assume that
1. `φ(X) = φt(X) ∧ φp(X)` where `φt(X)` is a function-like __term__
   and `φp(X)` is a predicate
1. `α(Z) = αt(Z) ∧ αp(Z)` where `αt(Z)` is a function-like __term__,
   and `αp(Z)` is a predicate
 
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
∀ X . φ(X) → ∃ Y . ψ(X, Y) ∨ •◆ ∃ Y . ψ(X, Y)`
```

We can now move `∃ Y . ψ(X, Y)` to the left of the implication,
and (assuming law of excluded middle) we obtain the equivalent:
```
∀ X . φ(X) ∧ ¬∃ Y . ψ(X, Y) → •◆ ∃ Y . ψ(X, Y)`
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

We assume that `φ(X)` and `α(Z)` are function-like formulae.

### Justification

```
φ(X) ∧ (¬ ∃ Z. α(Z))
    =  φ(X) ∧ (∀ Z. ¬α(Z))           -- ¬ ∃ = ∀ ¬
    =  ∀ Z. (φ(X) ∧ ¬α(Z))           -- φ(X) not depending on Z
    =  ∀ Z. (φ(X) ∧ ⌈φ(X) ∧ ¬α(Z)⌉)  -- φ(x) is function-like
    =  ∀ Z. (φ(X) ∧ ⌈φ(X)⌉ ∧ ¬⌈φ(X) ∧ α(Z)⌉) -- proven below
    =  ∀ Z. (φ(X) ∧ ¬⌈φ(X) ∧ α(Z)⌉)
    =  φ(X) ∧ (∀ Z. ¬⌈φ(X) ∧ α(Z)⌉)  -- φ(X) not depending on Z
    =  φ(X) ∧ (¬ ∃ Z. ⌈φ(X) ∧ α(Z)⌉) -- ¬ ∃ = ∀ ¬
```


### Missing details


#### `⌈φ ∧ ¬β⌉ = ⌈φ⌉ ∧ ¬⌈φ ∧ β⌉`

for any function-like formula `φ` and for any ML formula `β`.

__Proof:__
```
⌈φ ∧ ¬β⌉
    = ∃ x. x∈ (φ ∧ ¬β)
    = ∃ x. x∈ φ ∧ x∈ ¬β
    = ∃ x. x∈ φ ∧ ¬x∈ β 
    = ∃ x. x = φ ∧ ¬x∈ β  //φ is function-like
    = ∃ x. x = φ ∧ ¬φ∈ β  //substitution
    = (∃ x. x = φ) ∧ ¬φ∈ β
    = ⌈φ⌉ ∧ ¬φ∈ β  // properties of ⌈_⌉
    = ⌈φ⌉ ∧ ¬⌈φ ∧ β⌉  // definition of ∈ 
```


### Implementation concerns

We have shown above that

```
φ(X) ∧ (¬ ∃ Z. α(Z)) = φ(X) ∧ (¬ ∃ Z. ⌈φ(X) ∧ α(Z)⌉)
```

Now, if
1. `φ(X) = φt(X) ∧ φp(X)` where `φt(X)` is a function-like __term__
   and `φp(X)` is a predicate
1. `α(Z) = αt(Z) ∧ αp(Z)` where `αt(Z)` is a function-like __term__,
   and `αp(Z)` is a predicate
 
Then we can further expand the above as:
```
φ(X) ∧ (¬ ∃ Z. α(Z)) = φ(X) ∧ (¬ ∃ Z. ⌈φ(X) ∧ α(Z)⌉)
    =  φ(X) ∧ (¬ ∃ Z. ⌈φt(X) ∧ φp(X) ∧ αt(Z) ∧ αp(Z)⌉)
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
