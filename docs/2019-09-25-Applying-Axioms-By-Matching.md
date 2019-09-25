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
and there exists `t` such that
(3) `φₜ = αₜ(t)` and
(4) `φₚ → αₚ(t)`

Then, if we can show that
(5) `β(t) ∧ φₚ → ψ`

Then it is true that `φ → •ψ`.

### Proof

Premise (0) says
`∀ Y .α(Y) → •β(Y)`; instantiating `Y` with `t` we get
`α(t) → •β(t)` which is equivalent by (2) with
`αₜ(t) ∧ αₚ(t) → •β(t)`, and, by (3), with 
(6) `φₜ ∧ αₚ(t) → •β(t)`.

Premise (4) says
`φₚ → αₚ(t)`; by FOL reasoning (conjunction to left), we get
`φₜ ∧ φₚ → φₜ ∧ αₚ(t)`; by (5) and transitivity of `→`, we get
`φₜ ∧ φₚ → •β(t)`; by FOL reasoning we get
`φₜ ∧ φₚ → •β(t) ∧ φₚ`; due to (1') and properties of conjunction we get
`φₜ ∧ φₚ → •(β(t) ∧ φₚ)`, which is equivalent by (1) with
(7) `φ → •(β(t) ∧ φₚ)`.

Premise (5) says
`β(t) ∧ φₚ → ψ`; by the Framing rule of ML with `•`, we get
`•(β(t) ∧ φₚ) → •ψ`; by (7) and transitivity of `→`, we get
`φ → •ψ`.

QED


Equality axioms
---------------

Given an axiom of the form 
(0) `∀ Y . αₚ(Y) → αₜ(Y) = β(Y)`
and a goal `φ → ψ` such that 
(1) `φ` can be decomposed as `φ = φₜ ∧ φₚ`
and there exists `t` such that
(2) `φₜ = αₜ(t)` and
(3) `φₚ → αₚ(t)`

Then, if we can show that
(4) `β(t) ∧ φₚ → ψ`

Then it is true that `φ → ψ`.

### Proof

Premise (0) says
(0) `∀ Y . αₚ(Y) → αₜ(Y) = β(Y)`; instantiating `Y` with `t` we get
`αₚ(t) → αₜ(t) = β(t)` which is equivalent by (3) with
`αₚ(t) → φₜ = β(t)`; by (3) and transitivity of `→` we get
`φₚ → φₜ = β(t)`; by FOL reasoning (conjunction to left), we get
(5) `φₜ ∧ φₚ → φₜ ∧ (φₜ = β(t))`.


We can show that (see below)
`φₜ ∧ (φₜ = β(t)) ↔ β(t) ∧ (φₜ = β(t))`; by (5) and transitivity of `→`, we get
`φₜ ∧ φₚ → β(t) ∧ (φₜ = β(t))`; by FOL reasoning (dropping the second conjunct) we get
`φₜ ∧ φₚ → β(t)`; by FOL reasoning we get
`φₜ ∧ φₚ → β(t) ∧ φₚ`; by (4) and transitivity we get
`φₜ ∧ φₚ → ψ`, which is equivalent by (1) with
`φ → ψ`.

QED

#### Semantic proof for `φₜ ∧ (φₜ = β(t)) ↔ β(t) ∧ (φₜ = β(t))`

Say the interpretation of `φₜ` is `P` and the one of `β(t)` is `B`.

If `P` and `B` are equal, then the interpretation of `(φₜ = β(t))`
is the whole set, whence the interpretation of `φₜ ∧ (φₜ = β(t))` is `P` and
the interpretation of `β(t) ∧ (φₜ = β(t))` is `B`, thus they are equal.

If `P` and `B` are not equal, then the interpretation of `(φₜ = β(t))`
is the empty set, whence the interpretation of both `φₜ ∧ (φₜ = β(t))` and
`β(t) ∧ (φₜ = β(t))` is the empty set, thus they are equal.


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
we cannot soundly apply the algorithm above.

However,  if `⌈φₜ ∧ αₜ(Y)⌉` simplifies to a predicate of the form `(Y = t) ∧ p`
such that `p` is `⊤` (unification did not introduce extra constraints)
and if `t` verifies the conditions stated above, namely,

- `φₜ = αₜ(t)` (syntactic, not semantic, equality) and
- `φₚ → αₚ(t)` (validity, not satisfiability)

then we can replace the goal as per the usual algorithm
and set the remainder to `⊥`.

