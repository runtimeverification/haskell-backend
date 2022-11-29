Proving Total Correctness All-Path Reachability Claims
=====================================================

This document details Total Correctness All-Path Reachability.

_Prepared by Traian Șerbănuță and Virgil Șerbănuță,
based on [proving All-Path Reachability claims](2019-03-28-All-Path-Reachability-Proofs.md)_

Definitions
-----------

### All-path finally

Given a formula `φ`, let `AFφ` denote the formula “all-path finally” `φ`, whose
intended semantics is: "the set of configurations for which on all paths,
in a finite number of steps, `φ` holds".

In this section we will show that `AFφ` can be captured by the interpretation of
the fixed-point `μX.φ ∨ (○X ∧ •⊤)`

Let `Top` be the set of all configurations, and let `Prev` be the point-wise
extension of the function mapping a configuration to the set of all
configurations which can reach the given configuration in one step.
and `∁` be the complement operator on sets.

The semantics of `μX.φ ∨ (○X ∧ •⊤)` is `LFP(G)` where
```
G(X) := ⟦φ⟧ ∪ ( ∁(Prev(∁(X))) ∩ Prev(Top) )
```
Note that, since `X` is positively occurring in the scope of `μ`, `G` is
monotone, so the `LFP(G)` exists and can be defined according to the 
Knaster-Tarski formula, as the intersection of all pre-fixed-points of `G`,
that is, all `A` such that `G(A) ⊆ A`.

Let us also note that  `x ∈ G(A)` iff `φ` holds for `x` or `∅ ⊂ Prev⁻¹({x}) ⊆ A`.
Indeed,
```
x ∈ G(A) ⟺ × ∈ ⟦φ⟧ ∪ ( ∁(Prev(∁(A))) ∩ Prev(Top)
⟺ × ∈ ⟦φ⟧ or (x ∈ ∁(Prev(∁(A))) and x ∈ Prev(Top))
⟺ × ∈ ⟦φ⟧ or (¬ x ∈ Prev(∁(A)) and ∅ ⊂ Prev⁻¹({x}))
⟺ × ∈ ⟦φ⟧ or (¬ (∃y y ∈ ∁(A) ∧ x ∈ Prev(y)) and ∅ ⊂ Prev⁻¹({x}))
⟺ × ∈ ⟦φ⟧ or (¬ (∃y ¬y ∈ A ∧ x ∈ Prev(y)) and ∅ ⊂ Prev⁻¹({x}))
⟺ × ∈ ⟦φ⟧ or ((∀y y ∈ A ∨ ¬ x ∈ Prev(y)) and ∅ ⊂ Prev⁻¹({x}))
⟺ × ∈ ⟦φ⟧ or ((∀y x ∈ Prev(y) ⟹ y ∈ A) and ∅ ⊂ Prev⁻¹({x}))
⟺ × ∈ ⟦φ⟧ or (Prev⁻¹({x}) ⊆ A and ∅ ⊂ Prev⁻¹({x}))
⟺ × ∈ ⟦φ⟧ or (∅ ⊂ Prev⁻¹({x}) ⊆ A)
```

Let `stuck x` be defined as `Prev⁻¹(x) = ∅` and let `x τ y` be defined
as `y ∈ Prev⁻¹({x})`.
We can also express `∅ ⊂ Prev⁻¹({x}) ⊆ A` in terms
of `stuck` and transitions, as `¬ stuck x ∧ ∀y x τ y → y ∈ A`.
Hence, `x ∈ G(A)` if either `x` matches `φ`, or `x` is not stuck and all
its transitions go into `A`.

We can coinductively define (the possibly infinite) complete traces of the
transition system determined by `Prev⁻¹` starting in an element `a` as being:
either just `a`, if `stuck a`, or `a` followed by a trace starting in `b` for
some `b` such that `a τ b`.
Given this definition, the trace semantics for `AF φ` is
```
⟦AF φ⟧ ::= { a | forall tr trace starting in a, exists b in tr such that b ∈ ⟦φ⟧ }
```

Let us first argue that `⟦AF φ⟧` is a pre-fixed-point of `G`, i.e., that
`G(⟦AF φ⟧) ⊆ ⟦AF φ⟧`.
Take `a ∈ G(⟦AF φ⟧)`. Then either `a ∈ ⟦φ⟧` or `¬ stuck a` and for all `b`
such that `a τ b`, `b ∈ ⟦AF φ⟧`.
Let `tr` be a complete trace starting in `a`.
If `a ∈ ⟦φ⟧`, then we can choose precisely `a` as the witness on that trace 
for which `φ` holds.
Otherwise, `¬ stuck a` and for all `b` such that `a τ b`, `b ∈ ⟦AF φ⟧`.
Since `¬ stuck a` it must be that `tr` cannot be just `a` (it's complete), so
there must exist a `b` such that `a τ b` and `b` is the start of a trace `tr'`
such that `tr = a ⋅ tr'`. However, since `a τ b`, it follows that`b ∈ ⟦AF φ⟧`,
so `tr'` must contain a witness for which `φ` holds; that witness is also a
witness for `tr`.

Let us now argue that `⟦AF φ⟧` is a post-fixed-point of `G`, i.e., that
`⟦AF φ⟧ ⊆ G(⟦AF φ⟧)`.
Take `a ∈ ⟦AF φ⟧`. We need to prove that either `a ∈ ⟦φ⟧` or `¬ stuck a` and
for all `b` such that `a τ b`, `b ∈ ⟦AF φ⟧`,
If `φ` holds for `a` then we're done. Assume `a ∉ ⟦φ⟧`.
Then it must be that `¬ stuck a`, since otherwise `a` would be a complete trace
starting in `a` with no witness for which `φ` holds.
Let now `b` be such `a τ b`. We need to show that `b ∈ ⟦AF φ⟧`. Let `tr` be a
complete trace starting in `b`. Then `a ⋅ tr` is a complete trace starting in `a`.
Since `a ∈ ⟦AF φ⟧`, there must be a witness in `a ⋅ tr` for which `φ` holds.
However, since `φ` doesn't hold for `a`, the witness must be part of `tr`
Since `tr` was chosen arbitrarily, it must be that `a ∈ ⟦AF φ⟧`.

Therefore, `⟦AF φ⟧` is a fixed-point for `G`. To show that it is the LFP of `G` it
suffices to prove that it is included in any pre-fixed-point of `G`.
Let `A` be a pre-fixed-point of `G`, i.e., `G(A) ⊆ A`. That means that
(1) `A` contains all configurations matching `φ`; and
(2) `A` contains all configurations which are not stuck and transition on all
    paths into `A`
Assume by contradiction that there exists `a ∈ ⟦AF φ⟧` such that `a ∉ A`.
We will coinductively construct a complete trace starting in `a` with no
witness in `A`. Since `A` contains all configurations for which `φ` holds,
this would contradict the fact that  `a ∈ ⟦AF φ⟧`.
- if `stuck a` is stuck, then take the complete trace `a`
- if `¬ stuck a`, since `a ∉ A`, it means that (2) is false; hence it exists
  a transition `a τ b` such that `b ∉ A`. Then take the complete trace
  `a ⋅ tr` where `tr` is obtained by applying the above process for `b ∉ A`.

Hence, `⟦AF φ⟧ = ⟦μX.φ ∨ (○X ∧ •⊤)⟧`.

Justified by the above, in the sequel we will use `AF φ` to denote `μX.φ ∨ (○X ∧ •⊤)`.

A consequence of the above is that, by the deduction rules associated with `μ`,
`AF φ` can always be "unrolled" to `φ ∨ (○ AF φ ∧ •⊤)`.

### Total correctness all-path reachability claims

Given the definition of all-path finally discussed in the section above,
a total correctness all-path reachability claim is of the form
```
∀x.φ(x) → AF ∃z.ψ(x,z)
```
and basically states that from any configuration `γ` satisfying `φ(x)`
for some `x`, a configuration satisfying `ψ(x,z)` for some `z` will be reached
in a finite number of steps on any path.

If the system is finitely branching, the claim becomes stronger:
for any configuration `γ` satisfying `φ(x)` for some `x`, there exists a bound
on the number of steps required to reach a configuration satisfying `ψ(x,z)`
for some `z` on any path.
Since the configuration is reached after a finite number of steps,
such reachability claims guarantee termination, thus total correctness.

Problem Description
-------------------

Given a set of reachability claims, of the form `∀x.φ(x) → AF ∃z.ψ(x,z)`,
we are trying to prove all of them together, by well-founded induction on a
given `measure` defined on the quantified variables `x`.

The well-founded induction argument, which requires the `measure` to decrease before
applying a claim as an induction hypothesis, will replace the coinductive argument,
which requires that progress is made before applying a circularity.

## Proposal of syntax changes

- claims need to mention the other claims (including themselves) which are
  needed to complete their proof; this induces a dependency relation
- claims which are part of a dependency cycle (including self-dependencies)
  would need to be specified together as a "claim group"
- a claim group would need to provide a metric on their input variables;
  this metric must decrease whenever one tries to apply a claim from the group
  while proving a claim from the same group

A claim group would be something like 
```
claim group
  decreasing measure(x)

  . . .

  claim φᵢ(x) → AF ∃zᵢ.ψᵢ(x,zᵢ) [using(claimᵢ₁, ..., claimᵢₖ)]

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

For the algorithms derived from the present approach, please check the next section.

Assume we want to prove a group of claims defined over the same set of variables
`x`. Further assume that all other claims (which are not in the current group)
 on which these claims depend have already been proven.
 Assume also a given integer pattern `measure(x)`, over the same variables as
 the claims in the group.

Since we're proving all claims together, we can gather them in a single goal,
`P(x) ::= (φ₁(x) → AF ∃z.ψ₁(x,z)) ∧ ... ∧ (φₙ(x) → AF ∃z.ψₙ(x,z))`.

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
∀x. φᵢ(x) ∧ 0 ≤ measure(x) < measure(x₀) → AF ∃z.ψᵢ(x,z)
```

Similarly we can split the goal into a separate goal `φᵢ(x₀) → AF ∃z.ψᵢ(x₀,z)`
for each claim.

Since we might be using the claims to advance the proof of the claim, to avoid
confusion (and to reduce caring about indices) we will denote a goal with
`φ(x₀) → AF ∃z.ψ(x₀,z)` in all subsequent steps, although the exact goal might
change from one step to the next.

Moreover, we will consider the induction hypotheses to be derived claims to
be applied as circularities, and denote them as `∀x. φᵢ(x) → AF ∃z.ψᵢ(x,z)`,
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
and variables. This definition can be extended to include AC constructors, e.g.
map concatenation


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
φ(x₀) → AF ∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃z.ψ(x₀, z)) ∨ (φ(x₀) ∧ ¬∃z.ψ(x₀, z)) → AF ∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃z.ψ(x₀, z) → AF ∃z.ψ(x₀,z)) ∧ (φ(x₀) ∧  ¬∃z.ψ(x₀, z) → AF ∃z.ψ(x₀,z))
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
the form `∀x.φᵢ(x) → AF ∃z.ψᵢ(x,z)`, we will refer to all as extended claims.
Let `∀x.φᵢ(x) → AF ∃z.ψᵢ(x,z)` denote the ith induction hypothesis or already
proven claim.

```
φ(x₀) → AF ∃z.ψ(x₀,z)
φ(x₀) ∧ (∃x.φ₁(x) ∨ … ∨ ∃x.φₙ(x) ∨ (¬∃x.φ₁(x) ∧ … ∧ ¬∃x.φₙ(x))) → AF ∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃x.φ₁(x)) ∨ … ∨ (φ(x₀) ∧ ∃x.φₙ(x)) ∨ (φ(x₀) ∧ (¬∃x.φ₁(x) ∧ … ∧ ¬∃x.φₙ(x))) → AF ∃z.ψ(x₀,z)
(φ(x₀) ∧ ∃x.φ₁(x) → AF ∃z.ψ(x₀,z))  ∧ … (φ(x₀) ∧ ∃x.φₙ(x) → AF ∃z.ψ(x₀,z))
    ∧ (φ(x₀) ∧ (¬∃x.φ₁(x) ∧ … ∧ ¬∃x.φₙ(x)) → AF ∃z.ψ(x₀,z))
```

assuming that `⌈φ(x₀) ∧ φᵢ(x)⌉ ≡ (x = tᵢ(x₀)) ∧ pᵢ(x₀, x)` for each `i`,
the above is equivalent with:
```
(φ₁(t₁(x₀)) ∧ p₁(x₀, t₁(x₀)) → AF ∃z.ψ(x₀,z))  ∧ … (φₙ(tₙ(x₀)) ∧ pₙ(x₀, tₙ(x₀)) → AF∃z.ψ(x₀,z))
    ∧ (φ(x₀) ∧ ¬p₁(x₀, t₁(x₀)) ∧ … ∧ ¬pₙ(x₀, tₙ(x₀)) → AF ∃z.ψ(x₀,z))
```

This can be split into proving a goal for each extended claim,
```
φᵢ(tᵢ(x₀)) ∧ pᵢ(x₀, tᵢ(x₀)) → AF ∃z.ψ(x₀,z)
```
and one for the remainder
```
φ(x₀) ∧ ¬p₁(x₀, t₁(x₀)) ∧ … ∧ ¬pₙ(x₀, tₙ(x₀) → AF∃z.ψ(x₀,z))
```

Note that, in particular, part of the predicate of the remainder will include
the negation of the measure check for each induction hypothesis, of the form
`¬measure(tᵢ(x₀)) < measure(x₀)`.

#### Using a claim to advance the corresponding goal

Assume `φᵢ(tᵢ(x₀)) ∧ pᵢ(x₀, tᵢ(x₀)) → AF ∃z.ψ(x₀,z)` goal to be proven 
and let `∀x. φᵢ(x) → AF ∃z.ψᵢ(x,z)` be the corresponding extended claim.
By instatiating the claim with `x := tᵢ(x₀)`, we obtain
`φᵢ(tᵢ(x₀)) → AF ∃z.ψᵢ(tᵢ(x₀),z)`; then, by framing, we obtain
`φᵢ(tᵢ(x₀)) ∧ pᵢ(x₀, tᵢ(x₀)) → (AF ∃z.ψᵢ(tᵢ(x₀),z)) ∧ pᵢ(x₀, tᵢ(x₀))`.
Next, by predicate properties, we can obtain that
`φᵢ(tᵢ(x₀)) ∧ pᵢ(x₀, tᵢ(x₀)) → AF ∃z.(ψᵢ(tᵢ(x₀),z) ∧ pᵢ(x₀, tᵢ(x₀)))`.

We can use transitivity of `→` to replace the initial goal with
`AF ∃z.ψᵢ(tᵢ(x₀),z) ∧ pᵢ(x₀, tᵢ(x₀)) → AF ∃z.ψ(x₀,z)`
This goal can soundly be replaced with
`∀z.ψᵢ(tᵢ(x₀),z) ∧ pᵢ(x₀, tᵢ(x₀)) → AF ∃z.ψ(x₀,z)`
as proving this goal would ensure that the above also holds.

#### Summary of applying extended claims

By applying the extended claims, we will replace the existing goal with a set
consisting of a goal for each extended claim (some with the hypothesis equivalent
with `⟂`) and a remainder.

- Goals associated to extended claims: `∀z.ψᵢ(tᵢ(x₀),z) ∧ pᵢ(x₀, tᵢ(x₀)) → AF ∃z.ψ(x₀,z)`
- Goal associated to the remainder: `φ(x₀) ∧ ¬p₁(x₀, t₁(x₀)) ∧ … ∧ ¬pₙ(x₀, tₙ(x₀) → AF ∃z.ψ(x₀,z))`
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

  
## Appendix: Always finally as a Kleene fixed-point

Note that this appendix bears no relevance for the rest of the document; it is
kept here only for being related to an initial approach to this document.

Let us study when ⟦AF φ⟧ can be expressed according to Kleene's
least-fixed-point formula, i.e., when `LFP(G) = ⋃ₙGⁿ(∅)`.

Given a complete trace `tr`, let `trₙ` be the `n`th element of the trace, if
it exists. 

Let us now argue that, for any natural `n`, `Gⁿ⁺¹(∅)` denotes the set of
configurations for which, in at most `n` steps, on all paths, `φ` holds, i.e.,
```
Gⁿ⁺¹(∅) = { a | forall tr trace starting in a, exists k ≤ n such that trₖ ∈ ⟦φ⟧ }
```
We do that by induction on `n`:
- Base case:
    ```
    G(∅) = ⟦φ⟧ ∪ ( ∁(Prev(∁(∅))) ∩ Prev(Top) )
         = ⟦φ⟧ ∪ ( ∁(Prev(Top)) ∩ Prev(Top) )
         = ⟦φ⟧ ∪ ∅
         = ⟦φ⟧
         = {a | a ∈ ⟦φ⟧}
         = { a | forall tr trace starting in a, exists k ≤ 0 such that trₖ ∈ ⟦φ⟧}
    ```
- Induction case.
  `a ∈ Gⁿ⁺²(∅) = G(Gⁿ⁺¹(∅))` iff `φ` holds for `a` or `¬ stuck a` and forall b
  such that `a τ b`, `b ∈ Gⁿ⁺¹(∅)`.
  Let `tr` be a complete trace starting in `a`. If the trace is just `a`,
  then it must be that `a` is stuck, therefore `\phi` holds for `a` and since
  `0 ≤ n+1` we are done. Otherwise assume `tr = a ⋅ tr'` such that `tr'` is a
  complete trace starting in a configuration `b`. Then `a τ b`, hence `b ∈  Gⁿ⁺¹(∅)`.
  By the induction hypothesis, there exists  `k ≤ n` such that `tr'ₖ ∈ ⟦φ⟧`, hence
  `trₖ₊₁ ∈ ⟦φ⟧`.
  Conversely, let `a` be such that forall `tr` trace starting in a, there exists
  `k ≤ 0` such that `trₖ ∈ ⟦φ⟧`. If `a ∈ ⟦φ⟧`, then `a ∈ G(Gⁿ⁺¹(∅))`. Suppose
  `a ∉ ⟦φ⟧`. Then `¬ stuck a` (otherwise `a` would be a trace starting in `a`
  for which the hypothesis would not hold). Let `b` be such `a τ b`.

Since `G` is monotone, we can deduce that `Gⁿ(∅) ⊆ Gⁿ⁺¹(∅)`
(obviously `∅ ⊆ G(∅)` and then by applying monotone G `n` times).
Therefore, the limit `⋁ₙGⁿ(∅)` exists.

By the characterization of `Gⁿ(∅)` presented above, it follows that `⋁ₙGⁿ(∅)`
denotes the set of configurations for which there exists `n` such that in at
most `n` steps, on all paths, `φ` holds, i.e.,
```
⋁ₙGⁿ(∅) = { a | ∃ n, a ∈ Gⁿ⁺¹(∅)}
        = { a | ∃n ∀tr tr₀ = a → ∃k k ≤ n ∧ trₖ ∈ ⟦φ⟧ }
```
Note that there is a slight difference from the semantics intended for `AF φ`:
`⟦AF φ⟧ = { a | ∀tr tr₀ = a → ∃k trₖ ∈ ⟦φ⟧`

Nevertheless, it is relatively easy to see that `⋁ₙGⁿ(∅)` is a subset of `⟦AF φ⟧`,
hence, if we show that it is a fixed-point, then they would be equal.
Also, it's easy to see that `⋁ₙGⁿ(∅)` is a post-fixed-point.
We have that for all `n`, `Gⁿ(∅) ⊆ ⋁ₙGⁿ(∅)` and since `G` is monotone,
`Gⁿ⁺¹(∅) ⊆ G(⋁ₙGⁿ(∅))`. Also, obviously `G⁰(∅) = ∅ ⊆ G(⋁ₙGⁿ(∅))`.
Therefore, `⋁ₙGⁿ(∅) ⊆ G(⋁ₙGⁿ(∅))`.

It remains to show that `⋁ₙGⁿ(∅)` is a pre-fixed-point, i.e., that
`G(⋁ₙGⁿ(∅)) ⊆ ⋁ₙGⁿ(∅)`, or `G(⋁ₙGⁿ(∅)) ∖ ⋁ₙGⁿ(∅) = ∅`.
We have that:
```
x ∈ G(⋁ₙGⁿ(∅)) ∖ ⋁ₙGⁿ(∅)
⟺ x ∈ G(⋁ₙGⁿ(∅)) and x ∉ ⋁ₙGⁿ(∅)
⟺ (x ∈ ⟦φ⟧ or ¬ stuck x and ∀y x τ y → y ∈ ⋁ₙGⁿ(∅)) and x ∉ ⋁ₙGⁿ(∅)
⟺ ¬ stuck x and (∀y x τ y → y ∈ ⋁ₙGⁿ(∅)) and x ∉ ⋁ₙGⁿ(∅) (since ⟦φ⟧ ⊆ ⋁ₙGⁿ(∅))
```

Given the above relation, we deduce that a sufficient condition ensuring that
`G(⋁ₙGⁿ(∅)) ∖ ⋁ₙGⁿ(∅) = ∅` is that the transition system is finitely branching,
i.e., that `Prev⁻¹({x})` is finite for any `x`. Indeed, suppose 
there exists `x ∈ G(⋁ₙGⁿ(∅)) ∖ ⋁ₙGⁿ(∅)`. Then, it must hold that
`¬ stuck x` and `(∀y x τ y → y ∈ ⋁ₙGⁿ(∅))` and `x ∉ ⋁ₙGⁿ(∅)` 
Let `k`, `y₁`, ..., `yₖ` be such that `Prev⁻¹({x}) = {y₁, ..., yₖ}`.
For any `i`, `yᵢ ∈ Prev⁻¹({x})`, hence `x τ yᵢ`, therefore `∃nᵢ yᵢ ∈ Gⁿⁱ(∅)`.
Let `n₁`, ..., `nₖ` be such that `yᵢ ∈ Gⁿⁱ(∅)` for any `1≤i≤k`.
Let `m = 𝐦𝐚𝐱 {n₁, ... , nₖ}`. Since `(Gⁿ(∅))ₙ` is an ascending chain,
it follows that `yᵢ ∈ Gᵐ(∅)` for any `1≤i≤k`, 
whence `x ∈ Gᵐ⁺¹(∅)`, contradiction with the fact that `x ∉ ⋁ₙGⁿ(∅)`.

Nevertheless, before continuing, let
us give an example of a system and property for which the above construction is
not a fixed-point.

#### Counterexample for `⟦AF φ⟧ = ⋁ₙGⁿ(∅)`

Consider the following K theory

```
syntax KItem ::= "x"

rule Y:Int => Y -Int 1 requires Y>0
rule x => Y:Int ensures Y >= 0
```
(note that Y is free on the right-hand-side in the second rule, meaning that X
can transition into any positive integer).

and the claim `x → AF 0`

It is easy to see that any trace originating in `x` will reach `0` in a finite
number of steps. However, there is no bound on the number of steps needed for `x`
to reach `0`.
