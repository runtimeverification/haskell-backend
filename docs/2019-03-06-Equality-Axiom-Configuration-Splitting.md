Equality Axiom Configuration Splitting
======================================

Background
----------

Functions are defined through axioms of the type `∀ Z . α(Z) = β(Z)`. The same
axioms are used for `ceil` evaluation and for simplifying functions without
evaluating them.

These axioms are interpreted in a directional way, i.e. if we find `α(Z)`,
we can transform it into `β(Z)`.

In order to apply this axiom to a pattern `φ(X)`, we find a predicate
`P(X, Z)`, which can be `⊥` such that
```
(∃ Z . P(X, Z) ∧ φ(X)) = (∃ Z . P(X, Z) ∧ α(Z))
```
In other words:
```
(φ(X) ∧ ∃ Z . P(X, Z))
  = (∃ Z . P(X, Z) ∧ φ(X))  -- X is not quantified by ∃ Z
  = (∃ Z . P(X, Z) ∧ α(Z))  -- From the equation above
  = (∃ Z . P(X, Z) ∧ β(Z))  -- Since α(Z) = β(Z)
```

`P(X, Z)` usually contains a substitution which has an assignment for each
variable in `Z`. Note that here we don't require `P` to be maximal,
i.e. `P` does not have to be `⌈φ(X) ∧ α(Z)⌉`.

Also see `docs/2018-11-08-Configuration-Splitting-Simplification.md` for a
similar problem that involves rewriting axioms.

Problem
-------

Above I described how we can transform parts of a pattern
(`∃ Y . P(X, Y) ∧ α(Z)` being transformed to `∃ Y . P(X, Y) ∧ β(Z)`). The
main question is how to transform the entire pattern with, e.g., a function
definition.

Solution
--------

Let us assume that we have several axioms `∀ Z . αi(Z) = βi(Z)` which we think
we should apply together (e.g. they form a function definition).

We identify `Pi(X, Y)` such that
```
(∃ Z . Pi(X, Z) ∧ φ(X)) = (∃ Z . Pi(X, Z) ∧ αi(Z)).
```
Let
```
Qi(X) = (¬ ∃ Y . P1(X, Y)) ∧ ... ∧ (¬ ∃ Y . Pi(X, Y))
```
Then we evaluate `φ(X)` as follows:
```
φ(X)

    --| a = (a ∧ b) ∨ (a ∧ ¬b)
  = (φ(X) ∧ ∃ Y . P1(X, Y)) ∨ (φ(X) ∧ ¬ ∃ Y . P1(X, Y))

    --| Q1's definition
  = (φ(X) ∧ ∃ Y . P1(X, Y)) ∨ (φ(X) ∧ Q1(X))

    --| α1(Y) = β1(Y)
  = (∃ Y . P1(X, Y) ∧ β1(Z)) ∨ (φ(X) ∧ Q1(X))

    --| a = (a ∧ b) ∨ (a ∧ ¬b)
  = (∃ Y . P1(X, Y) ∧ β1(Z))
    ∨ (∃ Y . P2(X, Y) ∧ β2(Z) ∧ Q1(X))
    ∨ (φ(X) ∧ Q1(X)) ∧ (¬ ∃ Y . P2(X, Y)))

    --| Q2's definition
  = (∃ Y . P1(X, Y) ∧ β1(Z))
    ∨ (∃ Y . P2(X, Y) ∧ β2(Z) ∧ Q1(X))
    ∨ (φ(X) ∧ Q2(X))
...
  = (∃ Y . P1(X, Y) ∧ β1(Z))
    ∨ (∃ Y . P2(X, Y) ∧ β2(Z) ∧ Q1(X))
    ...
    ∨ (∃ Y . Pn(X, Y) ∧ βn(Z) ∧ Qn-1(X))
    ∨ (φ(X) ∧ Qn(X))
```

At the end, we usually expect that `⌈φ(X) ∧ Qn(X)⌉ = ⊥`. Currently
we only check whether `Qn(X) = ⊥`, but we may want to do more in the future.