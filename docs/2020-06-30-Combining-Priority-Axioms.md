Combining priority axioms
=========================

Background
----------

If we have this chain of axioms: `α₁(X₁)⇒β₁(X₁)` … `αₙ(Xₙ)⇒βₙ(Xₙ)` in which
all the LHS are *function-like* and *injection-based*, and all the RHS
except `βₙ(Xₙ)` are *function-like*, then their combined transition is

```
(⌈β₁(X₁)∧α₂(X₂)⌉ ∧ ⌈β₂(X₂)∧α₃(X₃)⌉ ∧ … ∧ ⌈βₙ₋₁(Xₙ₋₁)∧αₙ(Xₙ)⌉ ∧ α₁(X₁)) → ••…•βₙ(Xₙ)
```

Also see the [Combining Rewrite Axioms](2019-09-09-Combining-Rewrite-Axioms.md)
document.

Priorities allow writing case-based `K` code that closer resembles functional
languages, i.e. it allows saying things like "Apply this rule first,
if that doesn't work try this other one, if that also doesn't work try
this, and so on". The `owise` attribute is a special case of this.

For a rule `φ(X) ⇒ ψ(X) requires P(X) [priority p]` we take the all
rules at previous priorities:
```
φ₁(X) ⇒ ψ₁(X) requires P₁(X)
...
φn(X) ⇒ ψn(X) requires Pn(X)
```
and we encode the rule as:
```
    φ(X) ∧ P(X)
    ∧ ¬ (∃ X₁ . φ₁(X₁) ∧ P₁(X₁))
    ...
    ∧ ¬ (∃ Xn . φn(Xn) ∧ Pn(Xn))
    ⇒ ψ(X)
```

Also see the [Rewrite Rule Priorities](2020-06-22-Rewrite-Rule-Priorities.md)
document.

Applying the rules
------------------

We will examine how to compute `⌈β(X₁)∧α(X₂)⌉` where `β(X₁)` is the right
hand side of a random rewrite rule and `α(X₂)` is the left hand sight of
priority rewrite rule.

```
⌈β(X₁)∧α(X₂)⌉
= ⌈ β(X₁) ∧ φ(X) ∧ P(X)
    ∧ ¬ (∃ X₁ . φ₁(X₁) ∧ P₁(X₁))
    ...
    ∧ ¬ (∃ Xn . φn(Xn) ∧ Pn(Xn))
  ⌉
// If β(X₁) is total-function-like then β(X₁) ∧ φ(X) = β(X₁) ∧ ⌈β(X₁) ∧ φ(X)⌉
= ⌈ β(X₁) ∧ ⌈β(X₁) ∧ φ(X)⌉ ∧ P(X)
    ∧ ¬ (∃ X₁ . φ₁(X₁) ∧ P₁(X₁))
    ...
    ∧ ¬ (∃ Xn . φn(Xn) ∧ Pn(Xn))
  ⌉
// If P is a predicate then ⌈φ∧P⌉=⌈φ⌉∧P
= ⌈ β(X₁)
    ∧ ¬ (∃ X₁ . φ₁(X₁) ∧ P₁(X₁))
    ...
    ∧ ¬ (∃ Xn . φn(Xn) ∧ Pn(Xn))
  ⌉
  ∧ ⌈β(X₁) ∧ φ(X)⌉ ∧ P(X)
// φ(X) ∧ (¬ ∃ Z. α(Z)) = φ(X) ∧ (¬ ∃ Z. ⌈φ(X) ∧ α(Z)⌉)
// See the Justification section in
// 2018-11-08-Configuration-Splitting-Simplification.md
= ⌈β(X₁)
    ∧ ¬ (∃ X₁ . ⌈ β(X₁) ∧ φ₁(X₁) ∧ P₁(X₁) ⌉)
    ...
    ∧ ¬ (∃ Xn . ⌈ β(X₁) ∧ φn(Xn) ∧ Pn(Xn) ⌉)
  ⌉
  ∧ ⌈β(X₁) ∧ φ(X)⌉ ∧ P(X)
// If P is a predicate then ⌈φ∧P⌉=⌈φ⌉∧P
= ⌈β(X₁)
    ∧ ¬ (∃ X₁ . ⌈ β(X₁) ∧ φ₁(X₁) ⌉ ∧ P₁(X₁))
    ...
    ∧ ¬ (∃ Xn . ⌈ β(X₁) ∧ φn(Xn) ⌉ ∧ Pn(Xn))
  ⌉
  ∧ ⌈β(X₁) ∧ φ(X)⌉ ∧ P(X)
// If P is a predicate then ∃ X . P is a predicate
// If P is a predicate then ⌈φ∧P⌉=⌈φ⌉∧P
= ⌈β(X₁)⌉
  ∧ ¬ (∃ X₁ . ⌈ β(X₁) ∧ φ₁(X₁) ⌉ ∧ P₁(X₁))
  ...
  ∧ ¬ (∃ Xn . ⌈ β(X₁) ∧ φn(Xn) ⌉ ∧ Pn(Xn))
  ∧ ⌈β(X₁) ∧ φ(X)⌉ ∧ P(X)
// ⌈t⌉ ∧ ⌈ t ∧ s ⌉ = ⌈ t ∧ s ⌉
= ⌈β(X₁) ∧ φ(X)⌉ ∧ P(X)
  ∧ ¬ (∃ X₁ . ⌈ β(X₁) ∧ φ₁(X₁) ⌉ ∧ P₁(X₁))
  ...
  ∧ ¬ (∃ Xn . ⌈ β(X₁) ∧ φn(Xn) ⌉ ∧ Pn(Xn))
```

Usually, at least some of the existential clauses should disappear, because
unification, i.e. the `⌈ β(Xi) ∧ φi(Xi) ⌉` part, will probably either succeed
with a full substitution, or will fail. Of course, since we are using symbolic
inputs, this is not guaranteed.
