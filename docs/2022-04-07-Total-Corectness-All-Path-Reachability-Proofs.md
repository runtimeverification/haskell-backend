Proving Total Corectness All-Path Reachability Claims
=====================================================

This document details Total Corectness All-Path Reachability.

_Prepared by Traian Șerbănuță, based on [proving All-Path Reachability
claims](2019-03-28-All-Path-Reachability-Proofs.md)_

Definitions
-----------

In the following, by abuse of notation, we will identify a formula with the set
of configurations it denotes, thus equality between formulae would mean that
they are equisatisfiable (they denote the same set of configurations).

### All-path finally

Given a formula `φ`, let `AFφ` denote the formula “all-path finally” `φ`,
defined by:

```
AFφ := μX.φ ∨ (○X ∧ •⊤)
```

#### Semantics of `AFφ`

By the definition above, `AFφ` is semantically defined as `LFP(G)`, the
least-fix-point of the following mapping:

```
G(X) := φ ∨ (○X ∧ •⊤)
```

Note that `G(X)` can be interpreted as the union between the set of
configurations for which `φ` holds and those which are not stuck and whose all
possible transitions lead into `X`.

Since `AFφ` is a fixed-point of `G`, the identity `G(AFφ) = AFφ` holds, whence
`AFφ = φ ∨ (○AFφ ∧ •⊤)`.

Moreover, `G` is monotone (`X` occurs in a positive position) and we can show
that the conditions of Kleene's fixed-point theorem are satisfied:
`Gⁿ(⊥) ⊆ Gⁿ⁺¹(⊥)`, because `Gⁿ(⊥)` denotes the set of configurations for which
on all paths, in at most `n-1` steps, `φ` holds.

Let us argue the above by induction on `n-1`.
- Base case: `G(⊥) = φ ∨ (○⊥ ∧ •⊤) = φ ∨ (¬•¬⊥ ∧ •⊤) = φ ∨ (¬•⊤ ∧ •⊤) = φ ∨ ⊥ = φ`,
  so `G(⊥)` is the set of configurations for which `φ` holds.
- Induction case: Assuming `Gⁿ(⊥)` denotes the set of configurations for which
  on all paths, in at most `n-1` steps, `φ` holds, `Gⁿ⁺¹(⊥) = G(Gⁿ(⊥))` will be
  the union between the set of configurations for which `φ` holds and those
  which are not stuck and whose all possible transitions lead into  the set of
  configurations for which on all paths, in at most `n-1` steps, `φ` holds, but
  these are precisely the configurations for which on all paths, in at most `n`
  steps, `φ` holds.

From Kleene's theorem, `AFφ = ⋁ₙGⁿ(⊥)`, whence, a configuration is in `AFφ` iff
it is in `Gⁿ(⊥)` for some positive integer `n`. By the characterization of
`Gⁿ(⊥)` presented above, it follows that `AFφ` denotes the set of configurations
for which on all paths, in a finite number of steps, `φ` holds.

### Total corectness all-path reachability claims

Given this definition of all-path finally, a total corectness all-path
reachability claim is of the form
```
∀x.φ(x) → AF∃z.ψ(x,z)
```
and basically states that from any configuration `γ` satisfying `φ(x)`
for some `x`, a configuration satisfying `ψ(x,z)` for some `z` will be reached
in a finite number of steps on any path.

Since the configuration is reached after a finite number of steps,
such reachability claims guarantee total corectness.

Problem Description
-------------------

Given a set of reachability claims, of the form `∀x.φ(x) → AF∃z.ψ(x,z)`,
we are trying to prove all of them together, by well-founded induction on a
given `measure` defined on the quantified variables `x`.

The well-founded induction argument requiring the `measure` to decrease before
applying a claim as a circularity replaces the coinductive argument requiring
that progress is made before applying a circularity.

## Proposal of syntax changes

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

  claim φᵢ(x) → AF∃zᵢ.ψᵢ(x,zᵢ) [using(claimᵢ₁, ..., claimᵢₖ)]

  . . .

end claim group
```
where the claims referred to by the `using` attribute mention dependencies which
are not part of the cycle.

TODO(virgil): wouldn't it work to use the existing module syntax?
if so, `import` statements could replace `using` attributed.
Still, syntax for `decreasing` statements, and accounting for sharing the
variables would need to be implemented.

## Approach

For the algorithms derived by the present approach, please see next section.

Assume we want to prove a group of claims defined over the same set of variables
`x`. Further assume that all claims not in group on which these claims depend
have already been proven.  Assume also a given integer pattern `measure(x)`,
over the same variables as the claims in the group.

Since we're proving all claims together, we can gather them in a single goal,
`P(x) ::= (φ₁(x) → AF∃z.ψ₁(x,z)) ∧ ... ∧ (φₙ(x) → AF∃z.ψₙ(x,z))`.

A well-founded induction principle allowing to prove `P` using `measure` would
be of the form

```
  forall x0, (forall x, 0 <= measure(x) < measure(x0) -> P(x)) -> P(x0)
  ---------------------------------------------------------------------
                          forall x, P(x)
```

By the above induction principle, to prove `forall x, P(x)` it suffices to prove
`forall x0, (forall x, 0 <= measure(x) < measure(x0) -> P(x)) -> P(x0)`

Fixing an arbitrary instance `x₀` of the variables and assuming the induction
hypothesis `forall x, 0 <= measure(x) < measure(x0) -> P(x)`, we need to prove
`P(x₀)`.

By first-order manipulation we can transform the induction hypothesis for `P`
into a set of induction hypotheses, one for each claim:
```
∀x. φᵢ(x) ∧ 0 ≤ measure(x) < measure(x₀) → AF∃z.ψᵢ(x,z)
```

Similarly we can split the goal into a separate goal `φᵢ(x₀) → AF∃z.ψᵢ(x₀,z)`
for each claim.

Since we might be using the claims to advance the proof of the claim, to avoid
confusion (and to reduce caring about indices) we will denote a goal with
`φ(x₀) → AF∃z.ψ(x₀,z)` in all subsequent steps, although the exact goal might
change from one step to the next.

Moreover, we will consider the induction hypotheses to be derived claims to
be applied as circularities, and denote them as `∀x. φᵢ(x) → AF∃z.ψᵢ(x,z)`,
where `φᵢ(x)` also contains the guard `0 ≤ measure(x) < measure(x₀)`.

### Background on unification and remainders of unification

Similarly to the All-Path Reachability document, we assume all pattern variables
used in this document to be _extended function-like patterns_, that is patterns
which can be written as `t ∧ p` where the interpretation of `t` contains at most
one element and `p` is a predicate. Note that this definition is similar to that
of _constrained terms_ used in reachability logic literature except that it
allows their term part `t` to be undefined.

_Extended constructor patterns_ will be those extended function-like patterns
for which `t` is a functional term, composed out of constructor-like symbols
and variables.


__Note:__
Whenever `φ` is an extended function-like pattern with no variables from `z` and
`ψ(z)` is an extended constructor-like pattern, then
```
φ ∧ ∃z.ψ(z) ≡ ∃z.φ ∧ ψ(z) ≡ ∃z.ψ(z) ∧ ⌈φ ∧ ψ(z)⌉
```
and
```
φ ∧ ¬∃z.ψ = φ ∧ ¬∃z.⌈φ ∧ ψ(z)⌉
```

Moreover, we will assume that the unification condition `⌈φ ∧ ψ(z)⌉` can always
be computed to be of the form `(z = t) ∧  p(z)`, where

* `t`s are functional patterns with no free variables from `z`
    * i.e., `[t / z]` is a substitution.
* `p(z)` is a predicate

Note that `p` can be `⟂` to signify that unification failed.
Hence, whenever `φ` is an extended function-like pattern and `ψ(z)` is an
extended constructor-like pattern, we have the following equivalent patterns:
```
φ ≡ φ ∧ ⊤ ≡ φ ∧ (∃z.ψ(z) ∨ ¬∃z.ψ(z)) ≡ (φ ∧ ∃z.ψ(z)) ∨ (φ ∧ ¬∃z.ψ(z)) ≡ 
(∃z.φ ∧ ψ(z)) ∨ (φ ∧ ¬∃z.⌈φ ∧ ψ(z)⌉) ≡
(∃z.ψ(z) ∧ ⌈φ ∧ ψ(z)⌉) ∨ (φ ∧ ¬∃z.⌈φ ∧ ψ(z)⌉) ≡
(∃z.ψ(z) ∧ (z = t) ∧ p(z)) ∨ (φ ∧ ¬∃z.(z = t) ∧ p(z)) ≡
(ψ(t) ∧ p(t)) ∨ (φ ∧ ¬p(t))
```

Note that in the left disjunct we can eliminate the predicate part of `ψ(t)`
from `p(t)` (by idempotence, as it's already present in `ψ(t)`).
Similarly, in the right disjunct we can eliminate the predicate part of `φ`
from `p(t)` (by deMorgan, distributivity, and cancelation).

### Eliminating the conclusion

First, let us eliminate the case when the conclusion holds now. We have
the following sequence of equivalent claims:

```
φ(x₀) → AF∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃z.ψ(x₀, z)) ∨ (φ(x₀) ∧ ¬∃z.ψ(x₀, z)) → AF∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃z.ψ(x₀, z) → AF∃z.ψ(x₀,z)) ∧ (φ(x₀) ∧  ¬∃z.ψ(x₀, z) → AF∃z.ψ(x₀,z))
```

The first conjunct, `φ(x₀) ∧ ∃z.ψ(x₀, z) → AF∃z.ψ(x₀,z)` can be discharged by
unrolling `AF∃z.ψ(x₀,z)` to `∃z.ψ(x₀,z) φ ∨ (○AF∃z.ψ(x₀,z) ∧ •⊤)`, and then
using that `∃z.ψ(x₀, z)` appears in both lhs (as a conjunct) and rhs (as a
disjunct).

This reduces the above to proving the following remainder claim:

```
φ(x₀) ∧ ¬∃z.ψ(x₀, z) → AF∃z.ψ(x₀,z)
```

Note that `φ(x₀) ∧ ¬∃z.ψ(x₀, z)` is also an extended function-like pattern, as
it can be rewritten to be of the form `φ(x₀) ∧ ¬p(x₀, t(x₀))`
By abuse of notation, let `φ(x₀)` denote `φ(x₀) ∧ ¬∃z.ψ(x₀, z)` in the sequel.
If `φ(x₀)` is equivalent to `⊥`, then the implication holds and we are done.

### Applying (extended) claims

Since both circularities (induction hypotheses) and already proven claims are of
the form `∀x.φᵢ(x) → AF∃z.ψᵢ(x,z)`, we will refer to all as extended claims.
Let `∀x.φᵢ(x) → AF∃z.ψᵢ(x,z)` denote the ith induction hypothesis or already
proven claim.

```
φ(x₀) → AF∃z.ψ(x₀,z)
φ(x₀) ∧ (∃x.φ₁(x) ∨ … ∨ ∃x.φₙ(x) ∨ (¬∃x.φ₁(x) ∧ … ∧ ¬∃x.φₙ(x))) → AF∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃x.φ₁(x)) ∨ … ∨ (φ(x₀) ∧ ∃x.φₙ(x)) ∨ (φ(x₀) ∧ (¬∃x.φ₁(x) ∧ … ∧ ¬∃x.φₙ(x))) → AF∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃x.φ₁(x) → AF∃z.ψ(x₀,z))  ∧ … (φ(x₀) ∧ ∃x.φₙ(x) → AF∃z.ψ(x₀,z))
    ∧ (φ(x₀) ∧ (¬∃x.φ₁(x) ∧ … ∧ ¬∃x.φₙ(x)) → AF∃z.ψ(x₀,z))
```

assuming that `⌈φ(x₀) ∧ φᵢ(x)⌉ ≡ (x = tᵢ(x₀)) ∧ pᵢ(x₀, x)` for each `i`,
the above is equivalent with:
```
(φ₁(t₁(x₀)) ∧ p₁(x₀, t₁(x₀)) → AF∃z.ψ(x₀,z))  ∧ … (φₙ(tₙ(x₀)) ∧ pₙ(x₀, tₙ(x₀)) → AF∃z.ψ(x₀,z))
    ∧ (φ(x₀) ∧ ¬p₁(x₀, t₁(x₀)) ∧ … ∧ ¬pₙ(x₀, tₙ(x₀)) → AF∃z.ψ(x₀,z))
```

This can be split into proving a goal for each extended claim,
```
φᵢ(tᵢ(x₀)) ∧ pᵢ(x₀, tᵢ(x₀)) → AF∃z.ψ(x₀,z)
```
and one for the remainder
```
φ(x₀) ∧ ¬p₁(x₀, t₁(x₀)) ∧ … ∧ ¬pₙ(x₀, tₙ(x₀) → AF∃z.ψ(x₀,z))
```

Note that, in particular, part of the predicate of the remainder will include
the negation of the measure check for each induction hypothesis, of the form
`¬measure(tᵢ(x₀)) < measure(x₀)`.

#### Using a claim to advance the corresponding goal

Assume `φᵢ(tᵢ(x₀)) ∧ pᵢ(x₀, tᵢ(x₀)) → AF∃z.ψ(x₀,z)` goal to be proven 
and let `∀x. φᵢ(x) → AF∃z.ψᵢ(x,z)` be the corresponding extended claim.
By instatiating the claim with `x := tᵢ(x₀)`, we obtain
`φᵢ(tᵢ(x₀)) → AF∃z.ψᵢ(tᵢ(x₀),z)`; then, by framing, we obtain
`φᵢ(tᵢ(x₀)) ∧ pᵢ(x₀, tᵢ(x₀)) → (AF∃z.ψᵢ(tᵢ(x₀),z)) ∧ pᵢ(x₀, tᵢ(x₀))`.
Next, by predicate properties, we can obtain that
`φᵢ(tᵢ(x₀)) ∧ pᵢ(x₀, tᵢ(x₀)) → AF∃z.(ψᵢ(tᵢ(x₀),z) ∧ pᵢ(x₀, tᵢ(x₀)))`.

We can use transitivity of `→` to replace the initial goal with
`AF∃z.ψᵢ(tᵢ(x₀),z) ∧ pᵢ(x₀, tᵢ(x₀)) → AF∃z.ψ(x₀,z)`
This goal can soundly be replaced with
`∀z.ψᵢ(tᵢ(x₀),z) ∧ pᵢ(x₀, tᵢ(x₀)) → AF∃z.ψ(x₀,z)`
as proving this goal would ensure that the above also holds.

#### Summary of applying extended claims

By applying the extended claims, we will replace the existing goal with a set
consisting of a goal for each extended claim (some with the hypothesis equivalent
with `⟂`) and a remainder.

- Goals associated to extended claims: `∀z.ψᵢ(tᵢ(x₀),z) ∧ pᵢ(x₀, tᵢ(x₀)) → AF∃z.ψ(x₀,z)`
- Goal associated to the remainder: `φ(x₀) ∧ ¬p₁(x₀, t₁(x₀)) ∧ … ∧ ¬pₙ(x₀, tₙ(x₀) → AF∃z.ψ(x₀,z))`
  By abuse of notation, let `φ(x₀)` denote `φ(x₀) ∧ ¬p₁(x₀, t₁(x₀)) ∧ … ∧ ¬pₙ(x₀, tₙ(x₀)`

### Applying axioms

The remainder from the above step denotes the case in which the conclusion
doesn't hold now, and neither of the extended claims can be applied.

We'll try therefore to apply one step from the semantics.
Let `φ(x₀) → AF∃z.ψ(x₀,z))` be the remainder goal. We can unfold `AF` to obtain
the equivalent `φ(x₀) → ∃z.ψ(x₀,z) ∨ ((○AF∃z.ψ(x₀,z)) ∧ •⊤)`. Since we know
that conclusion doesn't hold for `φ(x₀)`, we can replace the goal by
`φ(x₀) →  (○AF∃z.ψ(x₀,z)) ∧ •⊤`, which is equivalent to
`(φ(x₀) →  ○AF∃z.ψ(x₀, z)) ∧ (φ(x₀) → •⊤)`

Therefore we need to check two things:

1. That `φ(x₀)` is not stuck
1. That `φ(x₀) →  ○AF∃z.ψ`

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
(∀z₁.∃x₁.ψ₁(x₁,z₁) ∧ ⌈φ(x₀) ∧ φ₁(x₁)⌉ → AF∃z.ψ(x₀,z)) ∧ … ∧ (∀zₙ.∃xₙ.ψₙ(xₙ,zₙ) ∧ ⌈φ(x₀) ∧ φₙ(xₙ)⌉ → AF∃z.ψ(x₀,z))
```

we can derive `φ(x₀) →  ○AF∃z.ψ(x₀,z)`

This would allow us to replace the goal `φ(x₀) →  ○AF∃z.ψ(x₀,z)` with the set of goals
```
{ ∀zᵢ.ψᵢ(tᵢ(x₀),zᵢ) ∧ pᵢ(tᵢ(x₀)) → AF∃z.ψ(x₀,z) : 1 ≤ i ≤ n }
```

_Proof:_

Apply `(STEP)` on `φ(x₀)`, and we obtain that
```
φ(x₀) → o ⋁ᵢ ∃xᵢ.⌈φ(x₀) ∧ φᵢ(xᵢ)⌉ ∧ ∃zᵢ.ψᵢ(xᵢ,zᵢ)
```

We can replace our goal succesively with:
```
o ⋁ᵢ ∃xᵢ.⌈φ(x₀) ∧ φᵢ(xᵢ)⌉ ∧ ∃zᵢ.ψᵢ(xᵢ,zᵢ) → ○AF∃z.ψ(x₀, z)  // transitivity of → 
⋁ᵢ ∃xᵢ.⌈φ(x₀) ∧ φᵢ(xᵢ)⌉ ∧ ∃zᵢ.ψᵢ(xᵢ,zᵢ) → AF∃z.ψ(x₀, z)  // framing on ○
∃xᵢ.⌈φ(x₀) ∧ φᵢ(xᵢ)⌉ ∧ ∃zᵢ.ψᵢ(xᵢ,zᵢ) → AF∃z.ψ(x₀, z) for all i
```

#### Summary of applying the claims

- Check that the remainder `φ(x₀) ∧ ¬p₁(t₁(x₀)) ∧ … ∧ ¬pₙ(tₙ(x₀)))` is equivalent to `⟂`
- Replace the goal `φ(x₀) →  ○AF∃z.ψ(x₀,z)` by the set of goals
  ```
  { ∀zᵢ.ψᵢ(tᵢ(x₀),zᵢ) ∧ pᵢ(tᵢ(x₀)) → AF∃z.ψ(x₀,z) : 1 ≤ i ≤ n }
  ```

## Algorithms
-------------

To apply circularities we have to ensure that the measure has decreased.
However, whenever circularities may be applied, we want to apply them
immediately (to allow skipping over loops/recursive calls), and to only apply
regular rules on the parts on which circularities cannot apply.

On the other hand, care should be taken when choosing the measure, to ensure
it actually holds whenever one needs to reenter a loop/call a recursive
function. Failing to have a good such measure would result in the circularities
never being applied and the proof looping (and branching) forever.


### Algorithm `proveAllPath`

__Input:__

- set of variables `x`
- claim group `(φ₁(x) → AF∃z.ψ₁(x,z)) ∧ ... ∧ (φₙ(x) → AF∃z.ψₙ(x,z))`
- decreasing `measure(x)`

__Output:__ Proved or Unproved

* Fix an instance `x₀` for the variables `x`
* Let `claims ::= { ∀ x . φᵢ(x) ∧ measure(x) <Int measure(x₀) → AF∃z.ψᵢ(x,z) }`
* For each claim `φᵢ(x₀) → AF∃z.ψᵢ(x₀,z)`
    * check that `φᵢ(x₀) → measure(x₀) >=Int 0`
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

* extended claims `{ ∀xᵢ.φᵢ → AF∃zᵢ.ψᵢ : 1 ≤ i ≤ n }`, or
* axioms `{ ∀xᵢ.φᵢ → •∃zᵢ.ψᵢ : 1 ≤ i ≤ n }`

__Output:__ `(Goals, goalᵣₑₘ)`

* Let `goalᵣₑₘ := φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xₙ.⌈φ∧φₙ⌉`
* Let `Goals := { ∀z₁.(∃x₁.ψ₁ ∧ ⌈φ∧φ₁⌉), … , ∀zₙ.(∃xₙ.ψₙ ∧ ⌈φ∧φₙ⌉) }`

__Note__: `∀zᵢ.(∃xᵢ.ψᵢ ∧ ⌈φ∧φᵢ⌉)` is obtained from
`(∃xᵢ.(∃zᵢ.ψᵢ) ∧ ⌈φ∧φᵢ⌉) → AF∃z.ψ`

__Note__: If the unfication condition `⌈φ ∧ φᵢ⌉ = (xᵢ=tᵢ)∧ pᵢ`
with `tᵢ` functional, `pᵢ` predicate, and `tᵢ` free of `xi`.
Then the goal `∀zᵢ.(∃xᵢ.ψᵢ ∧ ⌈φ∧φᵢ⌉) → AF∃z.ψ`
is equivalent to `∀zᵢ.ψᵢ[tᵢ/xᵢ] ∧ pᵢ[tᵢ/xᵢ] → AF∃z.ψ`.

Similarly `goalᵣₑₘ := (φ ∧ ¬∃x₁.⌈φ∧φ₁⌉ ∧ …  ∧ ¬∃xₙ.⌈φ∧φₙ⌉)`
is equivalent to `(φ ∧ ⋀ⱼ ¬pⱼ[tⱼ/xⱼ])`
where `j` ranges over the set `{ i : 1 ≤ i ≤ n, φ unifies with φᵢ }`.

__Note__: If `φ` does not unify with `φᵢ`, then `⌈φ∧φᵢ⌉ = ⊥`, hence
the goal `∀x∪zᵢ.(∃xᵢ.ψᵢ ∧ ⌈φᵢʳᵉᵐ∧φᵢ⌉) → AF∃z.ψ` is equivalent to
`∀x.⊥ → AF∃z.ψ` which can be discharged immediately. Also, in the
remainder `¬∃x₁.⌈φ∧φ₁⌉ = ⊤` so the conjunct can be removed.

