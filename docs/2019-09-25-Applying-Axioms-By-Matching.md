Algorithm for applying one rule to a pattern by matching
========================================================

This document presents an alternative way of applying axioms,
both rewrite- and equality- ones, which can be used when
the rule fully matches the configuration, thus having the advantage
that it does not produce remainders.

Since it makes no assumptions on the nature of the patterns involved,
it can safely be used when the configuration or the matching pattern
are __not__ function-like.

Rewrite rules
-------------

Given a rewrite axiom of the form 

(0) `∀ Y .α(Y) → •β(Y)`

and a goal `φ → •ψ` such that 

(1) `φ` can be decomposed as `φ = φₜ ∧ φₚ`, (1') `φₚ` predicate.

(2) `α(Y)` can be decomposed as `α(Y) = αₜ(Y) ∧ αₚ(Y)`

and there exist(s) functional pattern(s) `t` such that

(3) `φₚ → (φₜ = αₜ(t))` and

(4) `φₚ → αₚ(t)`

Then, if we can show that

(5) `β(t) ∧ φₚ → ψ`,

it is true that `φ → •ψ`.

### Proof


Premise (0) says

`∀ Y .α(Y) → •β(Y)`; instantiating `Y` with `t` (functional) we get

`α(t) → •β(t)` which is equivalent by (2) with

(6) `αₜ(t) ∧ αₚ(t) → •β(t)`.

From (3) and (4), by FOL reasoning (conclusions with same premise), we get

`φₚ → (φₜ = αₜ(t)) ∧ αₚ(t)`; by FOL reasoning (conjunction to left), we get

`φₜ ∧ φₚ → φₜ ∧ (φₜ = αₜ(t)) ∧ αₚ(t)`; by equality elimination we get

`φₜ ∧ φₚ → αₜ(t) ∧ αₚ(t)`; by (6) and transitivity of `→`, we get

`φₜ ∧ φₚ → •β(t)`; by FOL reasoning we get

`φₜ ∧ φₚ → •β(t) ∧ φₚ`; due to (1') and properties of conjunction we get

`φₜ ∧ φₚ → •(β(t) ∧ φₚ)`, which is equivalent by (1) with

(7) `φ → •(β(t) ∧ φₚ)`.

Premise (5) says

`β(t) ∧ φₚ → ψ`; by the Framing rule of ML with `•`, we get

`•(β(t) ∧ φₚ) → •ψ`; by (7) and transitivity of `→`, we get

`φ → •ψ`.

QED

### Coverage concerns (All-path-reachability)

Note that if `φ` and `αₜ(Y)` are not functional and constructor-based,
then the MGU migh not be computable.
In this case,  the above technique does not guarantee coverage as-is,
since `t` is not guaranteed to be the most general unifier
(there could be more than one minimal unifier).

The above reasoning could be extended to include multiple
substitution by replacing (3), (4) and (5) with something like

(3') `φₚ → (φₜ = αₜ(tᵢ))`, for i=1..n

(4') `φₚ → αₚ(tᵢ)`, for i=1..n

But it's not clear how to ensure completeness and link this
with the STEP rule. Also note that our usage of the STEP rule itself
in the proofs for the all-path algorithms assumes that `φ` is function-like.

Therefore the proposal for applying rewrite rules by matching described here
should not be used for all-path-reachability, at least not until we get a
better intuition.

Nevertheless, the proposal for equational axioms below does not suffer from the
same problem.

Equality axioms
---------------

Given an axiom of the form 

(0) `∀ Y . αₚ(Y) → (αₜ(Y) = β(Y))`

and a goal `φ → ψ` such that 

(1) `φ` can be decomposed as `φ = φₜ ∧ φₚ`

and there exist(s) functional pattern(s) `t` such that

(2) `φₚ → (φₜ = αₜ(t))` and

(3) `φₚ → αₚ(t)`

Then, if we can show that

(4) `β(t) ∧ φₚ → ψ`,

it is true that `φ → ψ`.

### Proof

Premise (0) says

(0) `∀ Y . αₚ(Y) → (αₜ(Y) = β(Y))`; instantiating `Y` with `t` (functional) we get

`αₚ(t) → (αₜ(t) = β(t))`; by (3) and transitivity of `→` we get

`φₚ → (αₜ(t) = β(t))`; by FOL (conjunctions with same premise) using (2) we get

`φₚ → (φₜ = αₜ(t)) ∧ (αₜ(t) = β(t))`; by FOL reasoning (conjunction to left), we get

`φₜ ∧ φₚ → φₜ ∧ (φₜ = αₜ(t)) ∧ (αₜ(t) = β(t))`; by equality elimination we get

`φₜ ∧ φₚ → αₜ(t) ∧ (αₜ(t) = β(t))`; by equality elimination we get

`φₜ ∧ φₚ → β(t)`; by FOL reasoning we get

`φₜ ∧ φₚ → β(t) ∧ φₚ`; by (4) and transitivity we get

`φₜ ∧ φₚ → ψ`, which is equivalent by (1) with

`φ → ψ`.

QED

### Coverage concerns (All-path-reachability)

Note that the original goal and the derived one only
differ in that `φₜ` and `β(t)`'s places are exchanged.
Because the equality is symmetric in (2) and `φₚ` is carried over to the
derived goal `φ → ψ` from `β(t) ∧ φₚ → ψ`.

Hence the derived goal is equivalent to the original one, so
all-path-reachability is not affected by the transformation.

Implementation concerns
-----------------------

Currently both rewrite axioms and equality axioms are applied following the ideas
described by 

- [Configuration Splitting Simplification](2018-11-08-Configuration-Splitting-Simplification.md)
  and
- [Applying axioms](2018-11-08-Applying-Axioms.md)

whose proof of soundness assumes that both `φₜ` and `αₜ(Y)` are _function-like_
and use the predicate `⌈φₜ ∧ αₜ(Y)⌉` to compute the substution and the remainder.

Assuming that one or both of `φₜ` and `αₜ(Y)` are __not__ function-like,
we cannot soundly apply the algorithms described in those documents.

However,  if `⌈φₜ ∧ αₜ(Y)⌉` simplifies to a predicate of the form `(Y = t) ∧ p`
and if `t` verifies the conditions stated above, namely,

- `φₚ → φₜ = αₜ(t)`
  * This could be checked syntactically (disregarding `φₚ`) or with an SMT (validity)
- `φₚ → αₚ(t)`
  * This could be checked with an SMT

then we can replace the goal as per the usual algorithm
and set the remainder to `⊥`.

Note: SMTs can prove validity of a formula by checking that its negation is
unsatisfiable.

### Multiple unifiers

If `⌈φₜ ∧ αₜ(Y)⌉` simplifies to a disjunctive predicate of the form
`((Y = t₁) ∧ p₁) ∨ ... ∨ ((Y = t₁) ∧ p₁)` then any of the `t` could be used to
verify the conditions above, since the algorithm works for any `t`.

Attempting to use each of them for the rewrite rules case
might increase chances of success for one-path-reachability.

Attempting to use each of them for equality axioms 
might reduce the need for unification modulo axioms later on.

For all-path, if there is a certainty that `t₁`, ..., `tₙ` are all possible 
substitutions such that `φₚ → φₜ = α(t)`, then verifying all derived goals 
could potentially constitute part of a completeness argument.

