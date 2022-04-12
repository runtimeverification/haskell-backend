Proving Full Correctness All-Path Reachability Claims
=====================================================

This document details Full Correctness All-Path Reachability without solving the
most-general-unifier (MGU) problem.
MGU will be detailed in a separate document.

_Prepared by Traian Șerbănuță, based on [proving All-Path Reachability
claims](2019-03-28-All-Path-Reachability-Proofs.md)_

Background
----------

Similarly to the All-Path Reachability document, we assume all pattern variables
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
    * i.e., `[t / z]` is a substitution.
* `p` is a predicate over `x ∪ z`

Under this assumption, `∃z.⌈φ ∧ ψ⌉` can be rewritten without the existential
quantification, as `p[t/z]`, i.e., `p` in which all ocurrences of the variables
from `z` are substituted with the corresponding term in `t`.


Definitions
-----------

### All-path finally

Given a formula `φ`, let `♢φ` denote the formula “all-path finally” `φ`,
defined by:

```
♢φ := μX.φ ∨ (○X ∧ •⊤)
```

one consequence of the above is that `♢φ ≡ φ ∨ (○♢φ ∧ •⊤)`.

Given this definition of all-path finally, a full correctness all-path
reachability claim
```
∀x.φ(x) → ♢∃z.ψ(x,z)
```
basically states that if `φ(x)` holds for a configuration `γ`, for some `x`,
then `P(γ)` holds, where `P(G)` is recursively defined on configurations as:
* there exists `z` such that `ψ(x,z)` holds for `G`
* or
    * `G` is not stuck (`G → • T`) and
    * `P(G')` for all configurations `G'` in which `G` can transition

__Note:__
Using the least fix-point (`μ`) instead of the greatest fix-point (`ν`)
restricts paths to finite ones. Therefore, the intepretation of a reachability
claim guarantees full-correctness, as it requires that the conclusion is
reached in a finite number of steps.

Problem Description
-------------------

Given a set of reachability claims, of the form `∀x.φ(x) → ♢∃z.ψ(x,z)`,
we are trying to prove all of them together.

### Additional complication

Since proving a claim now also needs to guarantee termination, there are several
extra requirements, as applications of circularities would now need to be
guarded by a measure of decreasingness instead of a measure of progress
(switching from coinduction to induction).

## Proposal of syntax changes to address the above mentioned complication

- claims need to mention the other claims (including themselves) which are
  needed to complete their proof; this induces a dependency relation
- claims which are part of a dependency cycle (including self-dependencies)
  would need to be specified together as a "claim group"
- a claim group would need to provide a metric on their input variables, which
  would be used as part of the decreasingness guard whenever one tries to apply
  a claim from the group during the proof of one the claims in the group

A claim group would be something like 
```
claim group
  decreasing measure(x)

  . . .

  claim φᵢ(x) → ♢∃zᵢ.ψᵢ(x,zᵢ) [using(claimᵢ₁, ..., claimᵢₖ)]

  . . .

end claim group
```

where the claims in the `using` mention the dependencies which are not part of
the cycle.

## Algorithms
-------------
(detailed in the next section)


### Algorithm `proveAllPath`

__Input:__ claim group `∀x. (φ₁(x) → ♢∃z.ψ₁(x,z)) ∧ ... ∧ (φₙ(x) → ♢∃z.ψₙ(x,z)) [decreasing measure(x)]`

__Output:__ Proved or Unproved

* Fix an instance `x₀` for the variables `x`
* Let `claims ::= { ∀ x . φᵢ(x) ∧ measure(x) <Int measure(x₀) → ♢∃z.ψᵢ(x,z) }`
* For each claim `φᵢ(x₀) → ♢∃z.ψᵢ(x₀,z)`
    * check that `φᵢ(x₀) → measure(x) >=Int 0`
    * Let `claimsᵢ ::= claims ∪ { claimᵢ₁, ..., claimᵢₖ }`
    * Let `Goals := { φᵢ(x₀) }`
    * While `Goals` is not empty:
        * Extract and remove `goal` of the form `φ` from `Goals`
        * Let `goalᵣₑₘ := φ ∧ ¬∃z.⌈φ ∧ ψᵢ⌉`
        * If `goalᵣₑₘ` is bottom (`goalᵣₑₘ ≡ ⊥`)
            * continue to the next goal
        * `(Goals', goal'ᵣₑₘ) := derivePar(goalᵣₑₘ, claimsᵢ)`
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
Then `goalᵣₑₘ := φ ∧ ¬∃z.⌈φ ∧ ψ⌉`
is equivalent to `φ ∧ ¬pᵢ[tᵢ/xᵢ]`.

### Algorithm `derivePar`

__Input:__: goal `φ` and set of tuples `{ (xᵢ,φᵢ,zᵢ,ψᵢ) : 1 ≤ i ≤ n }` representing either

* claims `{ ∀xᵢ.φᵢ → ♢∃zᵢ.ψᵢ : 1 ≤ i ≤ n }`, or
* axioms `{ ∀xᵢ.φᵢ → •∃zᵢ.ψᵢ : 1 ≤ i ≤ n }`

__Output:__ `(Goals, goalᵣₑₘ)`

* Let `goalᵣₑₘ := φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xₙ.⌈φ∧φₙ⌉`
* Let `Goals := { ∀z₁.(∃x₁.ψ₁ ∧ ⌈φ∧φ₁⌉), … , ∀zₙ.(∃xₙ.ψₙ ∧ ⌈φ∧φₙ⌉) }`

__Note__: `∀zᵢ.(∃xᵢ.ψᵢ ∧ ⌈φ∧φᵢ⌉)` is obtained from
`(∃xᵢ.(∃zᵢ.ψᵢ) ∧ ⌈φ∧φᵢ⌉) → ♢∃z.ψ`

__Note__: If the unfication condition `⌈φ ∧ φᵢ⌉ = (xᵢ=tᵢ)∧ pᵢ`
with `tᵢ` functional, `pᵢ` predicate, and `tᵢ` free of `xi`.
Then the goal `∀x∪zᵢ.(∃xᵢ.ψᵢ ∧ ⌈φ∧φᵢ⌉) → ♢∃z.ψ`
is equivalent to `∀x∪zᵢ.ψᵢ[tᵢ/xᵢ] ∧ pᵢ[tᵢ/xᵢ] → ♢∃z.ψ`.

Similarly `goalᵣₑₘ := (φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xₙ.⌈φ∧φₙ⌉)`
is equivalent to `(φ ∧ ⋀ⱼ ¬pⱼ[tⱼ/xⱼ])`
where `j` ranges over the set `{ i : 1 ≤ i ≤ n, φ unifies with φᵢ }`.

__Note__: If `φ` does not unify with `φᵢ`, then `⌈φ∧φᵢ⌉ = ⊥`, hence
the goal `∀x∪zᵢ.(∃xᵢ.ψᵢ ∧ ⌈φᵢʳᵉᵐ∧φᵢ⌉) → ♢∃z.ψ` is equivalent to
`∀x.⊥ → ♢∃z.ψ` which can be discharged immediately. Also, in the
remainder `¬∃x₁.⌈φ∧φ₁⌉ = ⊤` so the conjunct can be removed.


Explanation
-----------

Say we want to prove `∀x. (φ₁(x) → ♢∃z.ψ₁(x,z)) ∧ ... ∧ (φₙ(x) → ♢∃z.ψₙ(x,z)) [decreasing measure(x)]`.

We will do that by well-founded induction over `measure(x)`.
To do that, we would need to ensure that `measure(x)` is always positive;
this could be checked either syntactically, or using the SMT.

Fix an arbitrary instance `x₀` of the variables. We have to prove each
reachability claim `φᵢ(x₀) → ♢∃z.ψᵢ(x₀,z)`, using the induction hypothesis
`∀x. measure(x) < measure(x₀) → (φ₁(x) → ♢∃z.ψ₁(x,z)) ∧ ... ∧ (φₙ(x) → ♢∃z.ψₙ(x,z))`
which can be split into induction hypotheses for each claim
`∀x. φᵢ(x) ∧ measure(x) < measure(x₀) → ♢∃z.ψᵢ(x,z)`.

Since we might be using the claims to advance the proof of the claim, to avoid
confusion (and to reduce caring about indices) we will denote a goal with
`φ(x₀) → ♢∃z.ψ(x₀,z)` in all subsequent steps, although the exact goal might
change from one step to the next.

### Eliminating the conclusion

First, let us eliminate the case when the conclusion holds now. We have
the following sequence of equivalent claims:

```
φ(x₀) → ♢∃z.ψ(x₀,z)
φ(x₀) ∧ (∃z.ψ(x₀, z) ∨ ¬∃z.ψ(x₀, z)) → ♢∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃z.ψ(x₀, z)) ∨ (φ(x₀) ∧  ¬∃z.ψ(x₀, z)) → ♢∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃z.ψ(x₀, z) → ♢∃z.ψ(x₀,z)) ∧ (φ(x₀) ∧  ¬∃z.ψ(x₀, z) → ♢∃z.ψ(x₀,z))
```

The first conjunct, `φ(x₀) ∧ ∃z.ψ(x₀, z) → ♢∃z.ψ(x₀,z)` can be discharged by
unrolling `♢∃z.ψ(x₀,z)` to `∃z.ψ(x₀,z) φ ∨ (○♢∃z.ψ(x₀,z) ∧ •⊤)`, and then
using that `∃z.ψ(x₀, z)` appears in both lhs (as a conjunct) and rhs (as a
disjunct).

This reduces the above to proving the following remainder claim:

````
φ(x₀) ∧ ¬∃z.ψ(x₀, z) → ♢∃z.ψ(x₀,z)
```

Let `φ(x₀)` denote `φ(x₀) ∧ ¬(∃z.ψ(x₀, z))` in the sequel.
If `φ(x₀)` is equivalent to `⊥`, then the implication holds and we are done.

### Applying circularities (induction hypotheses)

To apply circularities we have to ensure that the measure has decreased.
However, whenever circularities may be applied, we want to apply them
immediately (to allow skipping over loops/recursive calls), and to only apply
regular rules on the parts on which circularities cannot apply.

On the other hand, care should be taken when choosing the measure, to ensure
it actually holds whenever one needs to reenter a loop/call a recursive
function. Failing to have a good such measure would result in the circularities
never being applied and the proof looping (and branching) forever.

In the following, let `∀x.φᵢ(x) → ♢∃z.ψᵢ(x,z)` denote the ith induction
hypothesis, with `φᵢ(x)` including the `measure(x) < measure(x₀)` check.

```
φ(x₀) → ♢∃z.ψ(x₀,z)
φ(x₀) ∧ (∃x.φ₁(x) ∨ … ∨ ∃x.φₙ(x) ∨ (¬∃x.φ₁(x) ∧ … ∧ ¬∃x.φₙ(x)) → ♢∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃x.φ₁(x)) ∨ … ∨ (φ(x₀) ∧ ∃x.φₙ(x)) ∨ (φ(x₀) ∧ (¬∃x.φ₁(x) ∧ … ∧ ¬∃x.φₙ(x))) → ♢∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃x.φ₁(x) → ♢∃z.ψ(x₀,z))  ∧ … (φ(x₀) ∧ ∃x.φₙ(x) → ♢∃z.ψ(x₀,z)) ∧ (φ(x₀) ∧ (¬∃x₁.φ₁ ∧ … ∧ ¬∃xₙ.φₙ)) → ♢∃z.ψ(x₀,z))
```

Note that the remainder can be rewritten using the following equivalences:

```
φ(x₀) ∧ (¬∃x.φ₁(x) ∧ … ∧ ¬∃x.φₙ(x)) → ♢ψ(x₀,z)
(φ(x₀) ∧ ¬∃x.φ₁(x)) ∧ … ∧ (φ(x₀) ∧ ¬∃x.φₙ(x)) → ♢ψ(x₀,z)
(φ(x₀) ∧ ¬∃x.⌈φ(x₀) ∧ φ₁(x)⌉) ∧ … ∧ (φ(x₀) ∧ ¬∃x.⌈φ(x₀)∧φₙ(x)⌉) → ♢ψ(x₀,z)
φ(x₀) ∧ (¬∃x.⌈φ(x₀) ∧ φ₁(x)⌉ ∧ … ∧  ¬∃x.⌈φ(x₀)∧φₙ(x)⌉) → ♢ψ(x₀,z)
```

In particular, part of the predicate of the remainder will include the negation
of the measure check, `¬measure(x) < measure(x₀)` instantiated with the
substitution associated with any term part of some `φᵢ(x)` matching `φ(x₀)`.

#### Using a claim to advance the corresponding goal

We want to prove that from the induction hypothesis `∀x. φᵢ(x) → ♢∃z.ψᵢ(x,z)`
and the derived goal `∀zᵢ.∃x.(ψᵢ(x,zᵢ) ∧ ⌈φ(x₀) ∧ φᵢ(x)⌉) → ♢∃z.ψ(x₀, z)`
we can deduce that `φ(x₀) ∧ ∃x.φᵢ(x) → ♢∃z.ψ(x₀,z)`.

This would allow us to replace goal `φ(x₀) ∧ ∃x.φᵢ(x) → ♢∃z.ψ(x₀,z)`
with goal `∀zᵢ.∃x.(ψᵢ(x,zᵢ) ∧ ⌈φ(x₀) ∧ φᵢ(x)⌉) → ♢∃z.ψ(x₀,z)`.

_Proof:_

The main step of our proof is to prove
`φ(x₀) ∧ ∃x.φᵢ(x) → ♢∃x.((∃zᵢ.ψᵢ(x,z)) ∧ ⌈φ(x₀) ∧ φᵢ(x)⌉)`
from `∀x. φᵢ(x) → ♢∃z.ψᵢ(x,z)`.

Assume `⌈φ(x₀) ∧ φᵢ(x)⌉ = (x=tᵢ(x₀))∧ pᵢ(x, x₀)` with `tᵢ(x₀)` functional and
free of `x` and `pᵢ(x₀,x)` predicate.

Then,
```
φᵢ(tᵢ) → ♢∃z.ψᵢ(tᵢ, z)                                                             // by induction hypothesis ∀x.φᵢ(x) → ♢∃z.ψᵢ(x,z) instantiated to x := tᵢ
φᵢ(tᵢ) ∧ p(x₀,tᵢ) → (♢∃z.ψᵢ(tᵢ, z)) ∧ p(x₀,tᵢ)                                     // framing
φᵢ(tᵢ) ∧ p(x₀,tᵢ) → ♢((∃z.ψᵢ(tᵢ, z)) ∧ p(x₀,tᵢ))                                   // predicate properties
∃x.φᵢ(x) ∧ x=tᵢ ∧ p(x₀,x) → ♢∃x.((∃z.ψᵢ(x,z)) ∧ x=tᵢ ∧ p(x₀,x))                    // substitution properties
∃x.φᵢ(x) ∧ ⌈φ(x₀)∧φᵢ(x)⌉ → ♢∃x.((∃z.ψᵢ(x,z)) ∧ ⌈φ(x₀)∧φᵢ(x)⌉)                      // definition of ⌈φ(x₀)∧φᵢ(x)⌉
φ(x₀) ∧ ∃x.φᵢ(x) ∧ ⌈φ(x₀)∧φᵢ(x)⌉ → ♢∃x.((∃z.ψᵢ(x,z)) ∧ ⌈φ(x₀)∧φᵢ(x)⌉)              // Strengthening
φ(x₀) ∧ ∃x.⌈φ(x₀) ∧ φᵢ(x) ∧ ⌈φ(x₀)∧φᵢ(x)⌉⌉ → ♢∃x.((∃z.ψᵢ(x,z)) ∧ ⌈φ(x₀)∧φᵢ(x)⌉)    // φ is functional
φ(x₀) ∧ ∃x.(⌈φ(x₀) ∧ φᵢ(x)⌉ ∧ ⌈φ(x₀)∧φᵢ(x)⌉) → ♢∃x.((∃z.ψᵢ(x,z)) ∧ ⌈φ(x₀)∧φᵢ(x)⌉)  // predicate properties
φ(x₀) ∧ ∃x.⌈φ(x₀) ∧ φᵢ(x)⌉ → ♢∃x.((∃z.ψᵢ(x,z)) ∧ ⌈φ(x₀)∧φᵢ(x)⌉)                    // idempotency
φ(x₀) ∧ ∃x.φᵢ(x) → ♢∃x.((∃z.ψᵢ(x,z)) ∧ ⌈φ(x₀)∧φᵢ(x)⌉)                              // φ is functional
```

#### Summary of applying circularities

By applying the circularities, we will replace the existing goal with a set
consisting of a goal for each circularity (some with the hypothesis equivalent
with `⟂`) and a remainder.

For a given induction hypothesis ``∀x. φᵢ(x) → ♢∃z.ψᵢ(x,z)`,
since `φ(x₀)` and `φᵢ(x)` are both function-like patterns (constrained terms),
we can assume that `⌈φ(x₀) ∧ φᵢ(x)⌉` can be written of the form 
`(x=tᵢ(x₀)) ∧ pᵢ(x, x₀)` with `tᵢ(x₀)` functional and free of `x` and
`pᵢ(x₀,x)` a predicate (which can be bottom to account for unification failure).

Then the derived goal associated to this induction hypothesis will be
`∀zᵢ.∃x.(ψᵢ(x,zᵢ) ∧ ⌈φ(x₀) ∧ φᵢ(x)⌉) → ♢∃z.ψ(x₀,z)`, which, using the above
identity, is equivalent to

```
∀zᵢ.∃x.(ψᵢ(x,zᵢ) ∧ (x=tᵢ(x₀)) ∧ pᵢ(x, x₀)) → ♢∃z.ψ(x₀,z)
∀zᵢ.∃x.(ψᵢ(tᵢ(x₀),zᵢ) ∧ pᵢ(tᵢ(x₀), x₀)) → ♢∃z.ψ(x₀,z)
∀zᵢ.ψᵢ(tᵢ(x₀),zᵢ) ∧ pᵢ(tᵢ(x₀), x₀) → ♢∃z.ψ(x₀,z)
```

Using the fact that the variables `zᵢ` only appear in the lhs, we can
instantiate them to arbitrary (but fixed) symbolic variables `z₀`, and then
let `φ(x₀)` denote ψᵢ(tᵢ(x₀),z₀) ∧ pᵢ(tᵢ(x₀), x₀)` for the next phase of the
algorithm.


### Applying axioms

We're back now to `φ(x₀) →  (○♢∃z.ψ(x₀,z)) ∧ •⊤`, which is equivalent to
`(φ(x₀) →  ○♢∃z.ψ(x₀, z)) ∧ (φ(x₀) → •⊤)`

Therefore we need to check two things:

1. That `φ(x₀)` is not stuck
1. That `φ(x₀) →  ○♢∃z.ψ`

Assume `∀xᵢ.φᵢ(xᵢ) →  •∃zᵢ.ψᵢ(xᵢ,zᵢ), 1 ≤ i ≤ n`  are all the one-step axioms
in the definition, and `P -> o ⋁ᵢ ∃xᵢ.⌈P ∧ φᵢ(xᵢ)⌉ ∧ ∃zᵢ.ψᵢ(xᵢ,zᵢ)`
is the STEP rule associated to them.

Using the same reasoning as when applying all claims in parallel,
`φ(x₀) → α` is equivalent with
```
(φ(x₀) ∧ ∃x₁.φ₁(x₁) → α) ∧ … ∧ (φ(x₀) ∧ ∃xₙ.φₙ(xₙ) → α) ∧ (φ(x₀) ∧ ¬∃x₁.φ₁(x₁) ∧ … ∧ ¬∃xₙ.φₙ(xₙ) → α)
```

Now, for the first thing to check, take `α := •⊤`.
Since all but the last conjunct are guaranteed to hold
(because of the rewrite axioms), `φ` is stuck if the remainder after attempting
to apply all axioms (i.e., the lhs of the last conjunct) is not equivalent to `⊥`.

We want to prove that from the STEP rule and 
```
(∀z₁.∃x₁.ψ₁(x₁,z₁) ∧ ⌈φ(x₀) ∧ φ₁(x₁)⌉ → ♢∃z.ψ(x₀,z)) ∧ … ∧ (∀zₙ.∃xₙ.ψₙ(xₙ,zₙ) ∧ ⌈φ(x₀) ∧ φₙ(xₙ)⌉ → ♢∃z.ψ(x₀,z))
```

we can derive `φ(x₀) →  ○♢∃z.ψ(x₀,z)`

This would allow us to replace the goal `φ(x₀) →  ○♢∃z.ψ(x₀,z)` with the set of goals
```
{ ∀zᵢ.∃xᵢ.ψᵢ(xᵢ,zᵢ) ∧ ⌈φ(x₀) ∧ φᵢ(xᵢ)⌉ → ♢∃z.ψ(x₀,z) : 1 ≤ i ≤ n }
```

_Proof:_

Apply `(STEP)` on `φ(x₀)`, and we obtain that
```
φ(x₀) → o ⋁ᵢ ∃xᵢ.⌈φ(x₀) ∧ φᵢ(xᵢ)⌉ ∧ ∃zᵢ.ψᵢ(xᵢ,zᵢ)
```

We can replace our goal succesively with:
```
o ⋁ᵢ ∃xᵢ.⌈φ(x₀) ∧ φᵢ(xᵢ)⌉ ∧ ∃zᵢ.ψᵢ(xᵢ,zᵢ) → ○♢∃z.ψ(x₀, z)  // transitivity of → 
⋁ᵢ ∃xᵢ.⌈φ(x₀) ∧ φᵢ(xᵢ)⌉ ∧ ∃zᵢ.ψᵢ(xᵢ,zᵢ) → ♢∃z.ψ(x₀, z)  // framing on ○
∃xᵢ.⌈φ(x₀) ∧ φᵢ(xᵢ)⌉ ∧ ∃zᵢ.ψᵢ(xᵢ,zᵢ) → ♢∃z.ψ(x₀, z) for all i
```

#### Summary of applying the claims

- Check that the remainder `φ(x₀) ∧ ¬∃x₁.φ₁(x₁) ∧ … ∧ ¬∃xₙ.φₙ(xₙ)` is equivalent to `⟂`
- Replace the goal `φ(x₀) →  ○♢∃z.ψ(x₀,z)` by the set of goals
  ```
  { ∀zᵢ.∃xᵢ.ψᵢ(xᵢ,zᵢ) ∧ ⌈φ(x₀) ∧ φᵢ(xᵢ)⌉ → ♢∃z.ψ(x₀,z) : 1 ≤ i ≤ n }
  ```

