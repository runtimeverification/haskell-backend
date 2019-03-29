Proving All-Path Reachability Claims
====================================

This document details All-Path Reachability without solving the
most-general-unifier (MGU) problem.
MGU will be detailed in a separate document.

Background
----------

Recommended reading: [proving One-Path Reachability
claims](2018-11-08-One-Path-Reachability-Proofs.md).

Similarly to the One-Path Reachability document, we assume all pattern variables
used in this document to be _extended function-like patterns_, that is patterns
which can be written as `t ∧ p` where the interpretation of `t` contains at most
one element and `p` is a predicate.

_Extended constructor patterns_ will be those extended function-like patterns
for which `t` is a functional term, composed out of constructor-like symbols
and variables.


Definitions
-----------

### Weak always

Given a formula `φ`, let `[w]φ` denote the formula “weak always” `φ`,
defined by:

```
[w]φ := νX.φ ∨ (○X ∧ •⊤)
```

one consequence of the above is that `[w]φ = φ ∨ (○[w]φ ∧ •⊤)`


Problem Description
-------------------

Given a set of claims of the form `∀x.φ(x) → ∃z.[w]ψ(x,z)`, we are trying to prove
all of them together.


Algorithms
----------
(detailed in the next section)


### Algorithm `proveAllPath`

__Input:__ claims `∀x₁.φ₁ → ∃z₁.[w]ψ₁`, `∀x₂.φ₂ → ∃z₂.[w]ψ₂`, …, `∀xₙ.φₙ → ∃zₙ.[w]ψₙ`

__Output:__ Proved or Unproved

* For each claim `∀x.φ → ∃z.[w]ψ`
    * Let `Goals := { ∀x.φ → ∃z.[w]ψ }`
    * While `Goals` is not empty:
        * Remove `goal` of the form `∀x.φ → ∃z.[w]ψ` from `Goals`
        * Let `goalᵣₑₘ := ∀x. (φ ∧ ¬∃z.⌈φ ∧ ψ⌉) → ∃z.[w]ψ`
        * If `goalᵣₑₘ` is trivialy valid (i.e., if `φ ∧ ¬∃z.⌈φ ∧ ψ⌉ = ⊥`)
            * continue to the next goal
        * If not the first while iteration for this claim:
            * `(Goals', goal'ᵣₑₘ) := deriveSeq(goalᵣₑₘ, claims)`
                (alternatively, one can use `(Goals', goal'ᵣₑₘ) := derivePar(goalᵣₑₘ, claims)`)
        * Else, let `(Goals', goal'ᵣₑₘ) := (∅, goalᵣₑₘ)`
        * Let `(Goals'', goal''ᵣₑₘ) := derivePar(goal'ᵣₑₘ, axioms)`
        * If `goal''ᵣₑₘ` is not trivially valid (its lhs is not `⊥`)
            * Return `Unprovable`
        * Let `Goals := Goals ∪ Goals' ∪ Goals''`
* Return `Provable`

### Algorithm `derivePar`

__Input:__: goal and set of claims/axioms

* goal: `∀x.φ → ∃z.[w]ψ`
* Either claims or axioms:
    * claims `∀x₁.φ₁ → ∃z₁.[w]ψ₁`, `∀x₂.φ₂ → ∃z₂.[w]ψ₂`, …, `∀xₙ.φₙ → ∃zₙ.[w]ψₙ`
    * axioms `∀x₁.φ₁ → ∃z₁.•ψ₁`, `∀x₂.φ₂ → ∃z₂.•ψ₂`, …, `∀xₙ.φₙ → ∃zₙ.•ψₙ`
    * we will not consider the form, but just the patterns and variables involved

__Output:__ `(Goals, goalᵣₑₘ)`

* Let `goalᵣₑₘ := ∀x.(φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xₙ.⌈φ∧φₙ⌉) → ∃z.[w]ψ`
* Let `Goals := { ∀x∪z₁.∃x₁.(ψ₁ ∧ ⌈φ∧φ₁⌉) → ∃z.[w]ψ, … , ∀x∪zₙ.∃xₙ.(ψₙ ∧ ⌈φ∧φₙ⌉) → ∃z.[w]ψ }`

### Algorithm `deriveSeq`

__Input:__: goal and set of claims/axioms

* goal: `∀x.φ → ∃z.[w]ψ`
* Either claims or axioms:
    * claims `∀x₁.φ₁ → ∃z₁.[w]ψ₁`, `∀x₂.φ₂ → ∃z₂.[w]ψ₂`, …, `∀xₙ.φₙ → ∃zₙ.[w]ψₙ`
    * axioms `∀x₁.φ₁ → ∃z₁.•ψ₁`, `∀x₂.φ₂ → ∃z₂.•ψ₂`, …, `∀xₙ.φₙ → ∃zₙ.•ψₙ`
    * we will not consider the form, but just the patterns and variables involved

__Output:__ `(Goals, goalᵣₑₘ)`

* Let `goalᵣₑₘ := ∀x.(φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xₙ.⌈φ∧φₙ⌉) → ∃z.[w]ψ`
* Let `Goals := { ∀x∪z₁.∃x₁.(ψ₁ ∧ ⌈φ1ʳᵉᵐ ∧φ₁⌉) → ∃z.[w]ψ, … , ∀x∪zₙ.∃xₙ.(ψₙ ∧ ⌈φnʳᵉᵐ φ∧φₙ⌉) → ∃z.[w]ψ }`

where `φ1ʳᵉᵐ := φ` and `φ(i+1)ʳᵉᵐ := φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xᵢ.⌈φ∧φᵢ⌉`


Explanation
-----------

Say we want to prove `∀x.φ → ∃z.[w]ψ`.

Unrolling `[w]ψ` we obtain `∀x.φ → ∃z.(ψ ∨ (○[w]ψ ∧ •⊤))`, or, equivalentely:
```
∀x.φ → (∃z.ψ) ∨ (∃z.○[w]ψ ∧ •⊤))
```


Moving `∃z.ψ` to the left of the implication, we get the equivalent

```
∀x. (φ ∧ ¬∃z.ψ) →  (∃z.○[w]ψ) ∧ •⊤
```

Let `φᵣₑₘ` be `φ ∧ ¬∃z.ψ`. This step eliminates the cases in which `∃z.ψ` holds now.

If `φᵣₑₘ` is `⊥`, then the implication holds and we are done.

### Simplifying `φ(x) ∧ ¬∃y.ψ(x,y)` where y does not appear in `φ(x)`

This process is detailed in
[Configuration Splitting Simplification](2018-11-08-Configuration-Splitting-Simplification.md).

Note: the process is quite similar to unification, and the result is either
`φ(X)`, if `φ(X)` and `ψ(X, Y)` are not unifiable, or
`φ(X) ∧ p(X)`, where `p(X)` is the negation of the predicate of `ψ(X, Y)`
on which the unifying substitution of `φ(X)` and `ψ(X, Y)` was applied, if
the two are unifiable.

Formally, the algorithm simplifies `φ(x) ∧ ¬∃y.ψ(x,y)` to `φ(x) ∧ ¬∃y.⌈φ(x) ∧ ψ(x,y)⌉`

### Applying circularities

To apply circularities we have to have made progress using regular rules.
However, whenever circularities may be applied, we want to apply them
immediately and to only apply regular rules on the parts on which
circularities cannot apply.

Therefore, if we are not at the first step in proving the claim,
we want to attempt applying all claims, similarly to how
we do that for the one-path reachability claims in the corresponding algorithm.

Doing so, we will obtain one result (maybe `⊥`) for each of the applied claims
and the remainder part, i.e., the part on which none of the claims
could be applied:

```
φ'ᵣₑₘ := φᵣₑₘ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ … ∧ ¬∃xₙ.⌈φ∧φₙ⌉ 
```

We have a chioce whether to apply circularities sequentially or in parallel.

#### Applying claims sequentially

```
∀x.φ → ∃z.[w]ψ                                            is equivalent to
∀x.φ ∧ (∃xᵢ.φᵢ ∨ ¬∃xᵢ.φᵢ) → ∃z.[w]ψ                       which is equivalent to
∀x.(φ ∧ ∃xᵢ.φᵢ) ∨ (φ ∧ ¬∃xᵢ.φᵢ) → ∃z.[w]ψ                 which is equivalent to
∀x.((φ ∧ ∃xᵢ.φᵢ) → [w]ψ) ∧ ∀x. ((φ ∧ ¬∃xᵢ.φᵢ) → ∃z.[w]ψ)  (1)
```

Note that the remainder `∀x.φ ∧ ¬∃xᵢ.φᵢ → ∃z.[w]ψ` can be rewritten as
`φ' ∧ ¬∃xᵢ.⌈φ'∧φᵢ⌉ → [w]ψ`, as detailed above.

__Note:__ If there are multiple claims which could apply on the same concrete
instance of a configuration, then applying them sequentially would reduce
the search space by potentially creating less goals.

If so, then `φ` for claim `i+1` would be
`φ(i+1)ʳᵉᵐ := φ ∧ ¬∃z.⌈φ∧ψ⌉ ∧ ¬∃x₁.⌈φ'∧φ₁⌉ ∧ …  ∧ ¬∃xᵢ.⌈φ'∧φᵢ⌉`

#### Applying claims in parallel

Note that in the above resoning we have used the idea that the remainder
is computed at every claim application; it is equally possible
to do it only once for all claims:

```
∀x.φ → ∃z.[q]ψ                                      
∀x.φ ∧ (∃x₁.φ₁ ∨ … ∨ ∃x₁.φₙ ∨ (¬∃x₁.φ₁ ∧ … ∧ ¬∃xₙ.φₙ) → ∃z.[w]ψ  
∀x.(φ ∧ ∃x₁.φ₁) ∨ … ∨ (φ' ∧ ∃xₙ.φₙ) ∨ (φ' ∧ (¬∃x₁.φ₁ ∧ … ∧ ¬∃xₙ.φₙ)) → ∃z.[w]ψ
(∀x.φ ∧ ∃x₁.φ₁ → ∃z.[w]ψ)  ∧ … (∀x.φ ∧ ∃xₙ.φₙ → ∃z.[w]ψ) ∧ (∀x.(φ ∧ (¬∃x₁.φ₁ ∧ … ∧ ¬∃xₙ.φₙ)) → ∃z.[w]ψ)
```

Note that the remainder can be rewritten as:

```
φ ∧ (¬∃x₁.φ₁ ∧ … ∧ ¬∃xₙ.φₙ) → [w]ψ
(φ ∧ ¬∃x₁.φ₁) ∧ … ∧ (φ ∧ ¬∃xₙ.φₙ) → [w]ψ
(φ ∧ ¬∃x₁.⌈φ ∧ φ₁⌉) ∧ … ∧ (φ ∧ ¬∃xₙ.⌈φ∧φₙ⌉) → [w]ψ
φ ∧ (¬∃x₁.⌈φ ∧ φ₁⌉ ∧ … ∧  ¬∃xₙ.⌈φ∧φₙ⌉) → [w]ψ
```

The advantage of this approach is that it's simpler, not altering the starting goal
from one derivation to the next.

#### Using a claim to advance the corresponding goal

Say we want to use the `∀xᵢ.φᵢ → ∃zᵢ.[w]ψᵢ` claim.
Note that `φ ∧ ∃xᵢ.φᵢ` is equivalent to `φᵢ ∧ ∃xᵢ.⌈φ'∧φᵢ⌉`, the second conjunct
being the substitution. We can therefore derive:

```
φᵢ ∧ ∃xᵢ.⌈φ'∧φᵢ⌉ → ∃zᵢ.[w]ψᵢ ∧ ∃xᵢ.⌈φ'∧φᵢ⌉ , and by using that `∃xᵢ.⌈φ'∧φᵢ⌉` is a predicate
φᵢ ∧ ∃xᵢ.⌈φ'∧φᵢ⌉ → ∃zᵢ.[w](ψᵢ ∧ ∃xᵢ.⌈φ'∧φᵢ⌉)    Therefore, 
φ ∧ φᵢ → ∃zᵢ.[w](ψᵢ ∧ ∃xᵢ.⌈φ'∧φᵢ⌉), and, by generalization,
∀x.φ ∧ φᵢ → ∃zᵢ.[w](ψᵢ ∧ ∃xᵢ.⌈φ'∧φᵢ⌉), and, by generalization,
```

Hence it is sound to replace the first conjunct in (1) by `∀x∪zᵢ.ψᵢ ∧ ∃xᵢ.⌈φ'∧φᵢ⌉ → [w]ψ`
because the "`→ [w]`" relation is transitive, and if the implication holds for all 
`zᵢ`, it will also hold for those derived from the claim.

### Applying axioms

We're back now to `∀x.φ →  (∃z.○[w]ψ) ∧ •⊤`, which is equivalent to 
`(∀x.φ →  ○[w]ψ) ∧ (∀x.φ →  •⊤)`

Therefore we need to check two things:

1. That `φ` is not stuck
1. That `∀x.φ →  ○[w]ψ`

Therefore, when using axioms to advance a goal, we want to find a `φ'`
such that `∀x.φ → •φ'` (making sure `φ` does not have any stuck parts)
and `φ' → ○φ'` (making sure that `φ'` covers everything `φ` can advance to).

If we have such a `φ'`, then it is sound to replace the goal by `∀x.φ' →  [w]ψ`
because

```
∀x.φ' → ∃z.[w]ψ   implies that
∀x.○φ' → ∃z.○[w]ψ  and using transity with ∀x.φ → ○φ' it implies that
∀x.φ → ∃z.○[w]ψ
```

Note also that we want a minimal such `φ'`, to maximize our chances to prove
the replacement goal; otherwise `⊤` would fit the description.

Now assuming `∀yᵢ.αᵢ →  •∃zᵢ.βᵢ, 1 ≤ i ≤ n`  are all the one-step axioms
in the definition, we can pick 
```
φ' := (∃y₁.⌈φ' ∧ α₁⌉ ∧ ∃z₁.β₁) ∨ … ∨ (∃yₙ.⌈φ' ∧ αₙ⌉ ∧ ∃zₙ.βₙ)
```
while also checking that the remainder
```
φ ∧ ¬(∃y.⌈φ ∧ α₁⌉) ∧ … ∧ ¬(∃y.⌈φ ∧ αₙ⌉)
```
is `⊥`, that is, that there is no stuck part of `φ`

That `φ'` can be chosen like this is a consequence of the __STEP__ axiom:
```
P -> o ((∃y₁.⌈P ∧ α₁⌉ ∧ ∃z₁.β₁) ∨ … ∨ (∃yₙ.⌈P ∧ αₙ⌉ ∧ ∃zₙ.βₙ))      (STEP)
```

Note that then it is sound to replace the goal `∀x.φ → ∃z.[w]ψ` with the conjunction of goals 
```
(∀x∪z₁.β₁ ∧ ∃y₁.⌈φ' ∧ α₁⌉ → ∃z.[w]ψ) ∧ … ∧ (∀x∪zₙ.βₙ ∧ ∃yₙ.⌈φ' ∧ αₙ⌉ → ∃z.[w]ψ)
```

