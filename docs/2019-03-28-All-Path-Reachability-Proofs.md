Proving All-Path Reachability Claims
====================================

This document details All-Path Reachability without solving the
most-general-unifier (MGU) problem.
MGU will be detailed in a separate document.

_Prepared by Traian Șerbănuță, Virgil Șerbănuță, Xiaohong Chen._

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


__Note:__
Whenever `φ` is a function-like pattern,
```
φ ∧ ∃z.ψ = φ ∧ ∃z.⌈φ ∧ ψ⌉
```
and
```
φ ∧ ¬∃z.ψ = φ ∧ ¬∃z.⌈φ ∧ ψ⌉
```

In this document we prefer the formulations on the right because they are of the
form pattern and predicate.

Moreover, suppose all free variables in the above formulae are from `x`,
we will assume that the unification condition `⌈φ ∧ ψ⌉` can always be
computed to be of the form `z = t ∧  p`, where

* `t`s are functional patterns with no free variables from `z`
    * i.e., [t / z] is a substitution.
* `p` is a predicate over `x ∪ z`

Under this assumption, `∃z.⌈φ ∧ ψ⌉` can be rewritten without the existential
quantification, as `p[t/z]`, i.e., `p` in which all ocurrences of the variables
from `z` are substituted with the corresponding term in `t`.


Definitions
-----------

### Weak always

Given a formula `φ`, let `[w]φ` denote the formula “weak always” `φ`,
defined by:

```
[w]φ := νX.φ ∨ (○X ∧ •⊤)
```

one consequence of the above is that `[w]φ = φ ∨ (○[w]φ ∧ •⊤)`.

Given this definition of weak always, an all-path reachability claim
```
∀x.φ(x) → [w]∃z.ψ(x,z)
```
basically states that if `φ(x)` holds for a configuration `γ`, for some `x`,
then `P(γ)` holds, where `P(G)` is recursively defined on configurations as:
* there exists `z` such that `ψ(x,z)` holds for `G`
* or
    * `G` is not stuck (`G → • T`) and
    * `P(G')` for all configurations `G'` in which `G` can transition



Problem Description
-------------------

Given a set of all-path reachability claims, of the form `∀x.φ(x) → [w]∃z.ψ(x,z)`,
we are trying to prove all of them together.


Algorithms
----------
(detailed in the next section)


### Algorithm `proveAllPath`

__Input:__ claims `∀x₁.φ₁ → [w]∃z₁.ψ₁`, `∀x₂.φ₂ → [w]∃z₂.ψ₂`, …, `∀xₙ.φₙ → [w]∃zₙ.ψₙ`

__Output:__ Proved or Unproved

* For each claim `∀x.φ → [w]∃z.ψ`
    * Let `Goals := { ∀x.φ → [w]∃z.ψ }`
    * While `Goals` is not empty:
        * Extract and remove `goal` of the form `∀x.φ → [w]∃z.ψ` from `Goals`
        * Let `goalᵣₑₘ := ∀x. (φ ∧ ¬∃z.⌈φ ∧ ψ⌉) → [w]∃z.ψ`
        * If `goalᵣₑₘ` is trivialy valid (i.e., if `φ ∧ ¬∃z.⌈φ ∧ ψ⌉ ≡ ⊥`)
            * continue to the next goal
        * If not the first while iteration for this claim:
            * `(Goals', goal'ᵣₑₘ) := deriveSeq(goalᵣₑₘ, claims)`
                (alternatively, one can use `(Goals', goal'ᵣₑₘ) := derivePar(goalᵣₑₘ, claims)`)
        * Else, let `(Goals', goal'ᵣₑₘ) := (∅, goalᵣₑₘ)`
        * Let `(Goals'', goal''ᵣₑₘ) := derivePar(goal'ᵣₑₘ, axioms)`
        * If `goal''ᵣₑₘ` is not trivially valid (its lhs is not equivalent to `⊥`)
            * Return `Unprovable`
        * Let `Goals := Goals ∪ Goals' ∪ Goals''`
* Return `Provable`

__Note:__ Since the derivation process can continue indefinitely, one could add
a bound on the total number of (levels of) expansions attempted before
returning `Unprovable`.

__Note__: If the unfication condition `⌈φ ∧ ψ⌉ = (z=t)∧ p`
with `t` functional, `p` predicate, and `t` free of `z`.
Then `goalᵣₑₘ := ∀x. (φ ∧ ¬∃z.⌈φ ∧ ψ⌉) → [w]∃z.ψ`
is equivalent to `∀x.φ ∧ ¬pᵢ[tᵢ/xᵢ] → [w]∃z.ψ`.

### Algorithm `derivePar`

__Input:__: goal `∀x.φ → [w]∃z.ψ` and set of tuples { (xᵢ,φᵢ,zᵢ,ψᵢ) : 1 ≤ i ≤ n }` representing either

* claims `{ ∀xᵢ.φᵢ → [w]∃zᵢ.ψᵢ : 1 ≤ i ≤ n }`, or
* axioms `{ ∀xᵢ.φᵢ → •∃zᵢ.ψᵢ : 1 ≤ i ≤ n }`

__Output:__ `(Goals, goalᵣₑₘ)`

* Let `goalᵣₑₘ := ∀x.(φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xₙ.⌈φ∧φₙ⌉) → [w]∃z.ψ`
* Let `Goals := { ∀x∪z₁.(∃x₁.ψ₁ ∧ ⌈φ∧φ₁⌉) → [w]∃z.ψ, … , ∀x∪zₙ.(∃xₙ.ψₙ ∧ ⌈φ∧φₙ⌉) → [w]∃z.ψ }`

__Note__: `∀x∪zᵢ.(∃xᵢ.ψᵢ ∧ ⌈φ∧φᵢ⌉) → [w]∃z.ψ` is obtained from
`∀x.(∃xᵢ.(∃zᵢ.ψᵢ) ∧ ⌈φ∧φᵢ⌉) → [w]∃z.ψ`

__Note__: If the unfication condition `⌈φ ∧ φᵢ⌉ = (xᵢ=tᵢ)∧ pᵢ`
with `tᵢ` functional, `pᵢ` predicate, and `tᵢ` free of `xi`.
Then the goal `∀x∪zᵢ.(∃xᵢ.ψᵢ ∧ ⌈φ∧φᵢ⌉) → [w]∃z.ψ`
is equivalent to `∀x∪zᵢ.ψᵢ[tᵢ/xᵢ] ∧ pᵢ[tᵢ/xᵢ] → [w]∃z.ψ`.


### Algorithm `deriveSeq`

__Input:__: goal and set of claims

* goal: `∀x.φ → [w]∃z.ψ`
* claims `∀x₁.φ₁ → [w]∃z₁.ψ₁`, `∀x₂.φ₂ → [w]∃z₂.ψ₂`, …, `∀xₙ.φₙ → [w]∃zₙ.ψₙ`

__Output:__ `(Goals, goalᵣₑₘ)`

* Let `goalᵣₑₘ := ∀x.(φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xₙ.⌈φ∧φₙ⌉) → [w]∃z.ψ`
* Let `Goals := { ∀x∪z₁.(∃x₁.ψ₁ ∧ ⌈φ₁ʳᵉᵐ∧φ₁⌉) → [w]∃z.ψ, … , ∀x∪zₙ.(∃xₙ.ψₙ ∧ ⌈φₙʳᵉᵐ∧φₙ⌉) → [w]∃z.ψ }`

where `φ₁ʳᵉᵐ := φ` and
```
φᵢ₊₁ʳᵉᵐ := φᵢʳᵉᵐ ∧ ¬∃xᵢ.⌈φ∧φᵢ⌉ = φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xᵢ.⌈φ∧φᵢ⌉
```

__Note__: If the unification condition `⌈φᵢʳᵉᵐ ∧ φᵢ⌉ = (xᵢ=tᵢ)∧ pᵢ`
with `tᵢ` functional, `pᵢ` predicate, and `tᵢ` free of `xi`.
Then the goal `∀x∪zᵢ.(∃xᵢ.ψᵢ ∧ ⌈φᵢʳᵉᵐ∧φᵢ⌉) → [w]∃z.ψ`
is equivalent to `∀x∪zᵢ.ψᵢ[tᵢ/xᵢ] ∧ pᵢ[tᵢ/xᵢ] → [w]∃z.ψ`.

Similarly `goalᵣₑₘ := ∀x.(φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xₙ.⌈φ∧φₙ⌉) → [w]∃z.ψ`
is equivalent to ∀x.(φ ∧ ⋀ⱼ ¬pⱼ[tⱼ/xⱼ]) → [w]∃z.ψ`
where `j` ranges over the set `{ i : 1 ≤ i ≤ n, φ unifies with φᵢ }`.

__Note__: If `φ` does not unify with `φᵢ`, then `⌈φ∧φᵢ⌉ = ⊥`, hence
the goal `∀x∪zᵢ.(∃xᵢ.ψᵢ ∧ ⌈φᵢʳᵉᵐ∧φᵢ⌉) → [w]∃z.ψ` is equivalent to
`∀x.⊥ → [w]∃z.ψ` which can be discharged immediately. Also, in the
remainder `¬∃x₁.⌈φ∧φ₁⌉ = ⊤` so the conjunct can be removed.


Explanation
-----------

Say we want to prove `∀x.φ → [w]∃z.ψ`.

Unrolling `[w]ψ` we obtain `∀x.φ → (∃z.ψ) ∨ (○[w]∃z.ψ ∧ •⊤)`.

Moving `∃z.ψ` to the left of the implication, we get the equivalent

```
∀x. (φ ∧ ¬∃z.ψ) →  ○[w](∃z.ψ) ∧ •⊤
```

Let `φᵣₑₘ` be `φ ∧ ¬∃z.ψ`. This step eliminates the cases in which `∃z.ψ` holds now.

If `φᵣₑₘ` is equivalent to `⊥`, then the implication holds and we are done.

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
∀x.φ → [w]∃z.ψ                                              is equivalent to
∀x.φ ∧ (∃xᵢ.φᵢ ∨ ¬∃xᵢ.φᵢ) → [w]∃z.ψ                         which is equivalent to
∀x.(φ ∧ ∃xᵢ.φᵢ) ∨ (φ ∧ ¬∃xᵢ.φᵢ) → [w]∃z.ψ                   which is equivalent to
∀x.((φ ∧ ∃xᵢ.φᵢ) → [w]∃z.ψ) ∧ ∀x. ((φ ∧ ¬∃xᵢ.φᵢ) → [w]∃z.ψ) (1)
```

Note that the remainder `∀x.φ ∧ ¬∃xᵢ.φᵢ → [w]∃z.ψ` can be rewritten as
`∀x.φ ∧ ¬∃xᵢ.⌈φ∧φᵢ⌉ → [w]∃z.ψ`, as detailed above.

__Note:__ If there are multiple claims which could apply on the same concrete
instance of a configuration, then applying them sequentially would reduce
the search space by potentially creating less goals.

If so, then `φ` for claim `i+1` would be
`φᵢ₊₁ʳᵉᵐ := φ ∧ ¬∃z.⌈φ∧ψ⌉ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xᵢ.⌈φ∧φᵢ⌉`

#### Applying claims in parallel

Note that in the above resoning we have used the idea that the remainder
is computed at every claim application; it is equally possible
to do it only once for all claims:

```
∀x.φ → [w]∃z.ψ
∀x.φ ∧ (∃x₁.φ₁ ∨ … ∨ ∃x₁.φₙ ∨ (¬∃x₁.φ₁ ∧ … ∧ ¬∃xₙ.φₙ) → [w]∃z.ψ  
∀x.(φ ∧ ∃x₁.φ₁) ∨ … ∨ (φ' ∧ ∃xₙ.φₙ) ∨ (φ' ∧ (¬∃x₁.φ₁ ∧ … ∧ ¬∃xₙ.φₙ)) → [w]∃z.ψ
(∀x.φ ∧ ∃x₁.φ₁ → [w]∃z.ψ)  ∧ … (∀x.φ ∧ ∃xₙ.φₙ → [w]∃z.ψ) ∧ (∀x.(φ ∧ (¬∃x₁.φ₁ ∧ … ∧ ¬∃xₙ.φₙ)) → [w]∃z.ψ)
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

We want to prove that from
```
∀xᵢ.φᵢ → [w]∃zᵢ.ψᵢ
∀x∪zᵢ.ψᵢ ∧ ∃xᵢ.⌈φ ∧ φᵢ⌉ → [w]ψ
```
we can deduce that `∀x.φ ∧ ∃xᵢ.φᵢ → [w]∃z.ψ`.

This would allow us to replace goal `∀x.φ ∧ ∃xᵢ.φᵢ → [w]∃z.ψ`
with goal '∀x∪zᵢ.∃xᵢ.ψᵢ ∧ ⌈φ ∧ φᵢ⌉ → [w]ψ'.

_Proof:_

The main step of our proof is to prove
`φ ∧ ∃xᵢ.φᵢ → [w]∃xᵢ.((∃zᵢ.ψᵢ) ∧ ⌈φ ∧ φᵢ⌉)`
from `∀xᵢ.φᵢ → [w]∃zᵢ.ψᵢ`.

Assume `⌈φ ∧ φᵢ⌉ = (xᵢ=tᵢ)∧ pᵢ` with `tᵢ` functional, `pᵢ` predicate, and
`tᵢ` free of `xi`.

Then,
```
φᵢ[tᵢ/xᵢ] → [w]∃zᵢ.ψᵢ[tᵢ/xᵢ]                              // by axiom ∀xᵢ.φᵢ → [w]∃zᵢ.ψᵢ instanțiated to xᵢ = tᵢ
φᵢ[tᵢ/xᵢ] ∧ p[tᵢ/xᵢ] → ([w]∃zᵢ.ψᵢ[tᵢ/xᵢ]) ∧ p[tᵢ/xᵢ]      // framing
φᵢ[tᵢ/xᵢ] ∧ p[tᵢ/xᵢ] → [w]((∃zᵢ.ψᵢ[tᵢ/xᵢ]) ∧ p[tᵢ/xᵢ])    // predicate properties
∃xᵢ.φᵢ ∧ xᵢ=tᵢ ∧ p → [w]∃xᵢ.((∃zᵢ.ψᵢ) ∧ xᵢ=tᵢ ∧ p)        // substitution properties
∃xᵢ.φᵢ ∧ ⌈φ∧φᵢ⌉ → [w]∃xᵢ.((∃zᵢ.ψᵢ) ∧ ⌈φ∧φᵢ⌉)              // definition of ⌈φ∧φᵢ⌉
φ ∧ ∃xᵢ.(φᵢ ∧ ⌈φ∧φᵢ⌉) → [w]∃xᵢ.((∃zᵢ.ψᵢ) ∧ ⌈φ∧φᵢ⌉)        // Strengthening
φ ∧ ∃xᵢ.⌈φ ∧ φᵢ ∧ ⌈φ∧φᵢ⌉⌉) → [w]∃xᵢ.((∃zᵢ.ψᵢ) ∧ ⌈φ∧φᵢ⌉)   // φ is functional
φ ∧ ∃xᵢ.(⌈φ∧φᵢ⌉ ∧ ⌈φ∧φᵢ⌉) → [w]∃xᵢ.((∃zᵢ.ψᵢ) ∧ ⌈φ∧φᵢ⌉)    // predicate properties
φ ∧ ∃xᵢ.⌈φ∧φᵢ⌉ → [w]∃xᵢ.((∃zᵢ.ψᵢ) ∧ ⌈φ∧φᵢ⌉)               // idempotency
φ ∧ ∃xᵢ.φᵢ → [w]∃xᵢ.((∃zᵢ.ψᵢ) ∧ ⌈φ∧φᵢ⌉)                   // φ is functional
```

### Applying axioms

We're back now to `∀x.φ →  (○[w]∃z.ψ) ∧ •⊤`, which is equivalent to
`(∀x.φ →  ○[w]∃z.ψ) ∧ (∀x.φ →  •⊤)`

Therefore we need to check two things:

1. That `φ` is not stuck
1. That `∀x.φ →  ○[w]∃z.ψ`

Assume `∀xᵢ.φᵢ →  •∃zᵢ.ψᵢ, 1 ≤ i ≤ n`  are all the one-step axioms
in the definition.

Using the same reasoning as in when applying all claims in parallel,
`∀x.φ → α` is equivalent with
```
(∀x.φ ∧ ∃x₁.φ₁ → α) ∧ … ∧ (∀x.φ ∧ ∃xₙ.φₙ → α) ∧ (∀x.φ ∧ ¬∃x₁.φ₁ ∧ … ∧ ¬∃xₙ.φₙ → α)
```

Now, for the first thing to check, take `α := •⊤`.
Since all but the last conjunct are guaranteed to hold
(because of the rewrite axioms), `φ` is stuck if the remainder after attempting
to apply all axioms (i.e., the lhs of the last conjunct) is not equivalent to `⊥`.

We want to prove that from
```
(∀x∪z₁.∃x₁.ψ₁ ∧ ⌈φ ∧ φ₁⌉ → [w]∃z.ψ) ∧ … ∧ (∀x∪zₙ.∃xₙ.ψₙ ∧ ⌈φ ∧ φₙ⌉ → [w]∃z.ψ)
P -> o ((∃x₁.⌈P ∧ φ₁⌉ ∧ ∃z₁.ψ₁) ∨ … ∨ (∃xₙ.⌈P ∧ φₙ⌉ ∧ ∃zₙ.ψₙ))      (STEP)
∀xᵢ.φᵢ →  •∃zᵢ.ψᵢ, 1 ≤ i ≤ n
```

we can derive
```
∀x.φ →  ○[w]∃z.ψ
```

This would allow us to replace the goal `∀x.φ →  ○[w]∃z.ψ` with the set of goals
```
{ ∀x∪zᵢ.∃xᵢ.ψᵢ ∧ ⌈φ ∧ φᵢ⌉ → [w]∃z.ψ : 1 ≤ i ≤ n }
```

_Proof:_

Apply `(STEP)` on `φ`, and we obtain that
```
φ → o ⋁ᵢ ∃xᵢ.⌈φ ∧ φᵢ⌉ ∧ ∃zᵢ.ψᵢ
```
And our proof goal becomes:
```
o ∨_i ∃xᵢ.⌈φ ∧ φᵢ⌉ ∧ ∃zᵢ.ψᵢ → ○[w]∃z.ψ
∨_i ∃xᵢ.⌈φ ∧ φᵢ⌉ ∧ ∃zᵢ.ψᵢ → [w]∃z.ψ  // framing on ○
∃xᵢ.⌈φ ∧ φᵢ⌉ ∧ ∃zᵢ.ψᵢ → [w]∃z.ψ  for all i
```

