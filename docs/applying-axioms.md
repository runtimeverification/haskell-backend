Algorithm for applying one rule to a pattern
============================================

**Input:** `φ(X)`, `∀ Y .α(Y) -> •β(Y)`

Note: • is "strong next" in this document

**Output:** a pattern `φ'(X)` satisfying the same assumptions we put on
  `φ(X)` such that
```
φ(X) ∧ (∃ Y . α(Y)) -> •φ'(X)
```

**Algorithm:**

1. Call *And Simplification* on `φ(X) ∧ α(Y)` to obtain a functional
   pattern  `t(X,Y)`, a substitution `subst(X,Y)`, and a predicate `p(X,Y)`.
 
   Note: if the unification fails, then `p(X,Y)` will be `⊥`

   Note: `\ceil(α(Y) ∧ φ(X)) = subst(X,Y) ∧ p(X,Y)`
   (by Prop 5.12 and \ceil(t) = \top)
1. Call *Simplification Procedure* on `∃ Y . (subst(X,Y) ∧ p(X,Y) ∧ β(Y))`
   and obtain a pattern `φ'(X)` *without existential quantification*.
1. Return `φ'(X)`

**Proof Object Generation.**

1. `α(Y) -> •β(Y)` // by axiom
1. `α(Y) ∧ \ceil(α(Y) ∧ φ(X)) -> (•β(Y)) ∧ \ceil(α(Y) ∧ φ(X))`
        // by (1) and propositional reasoning
1. `α(Y) ∧ \ceil(α(Y) ∧ φ(X)) = α(Y) ∧ φ(X)` // by ML paper Prop. 5.24
1. `α(Y) ∧ φ(X) -> (•β(Y)) ∧ \ceil(α(Y) ∧ φ(X))` // by (2) and (3)
1. `α(Y) ∧ φ(X) = t(X,Y) ∧ subst(X,Y) ∧ p(X,Y)` // by Unification Procedure
1. `α(Y) ∧ φ(X) -> subst(X,Y) ∧ p(X,Y) ∧ •β(Y)` // by (4) (5)
1. `α(Y) ∧ φ(X) -> ∃ Y . (subst(X,Y) ∧ p(X,Y) ∧ •β(Y))`
        // by (7) FOL reasoning
1. `α(Y) ∧ φ(X) -> •(∃ v . (β(Y) ∧ subst(X,Y) ∧ p(X,Y)))`
        // by (8) Propagation
1. `∃ Y . (β(Y) ∧ subst(X,Y) ∧ p(X,Y)) = φ'(X)`
        // by (recursively calling) *Basic Simplification*
1. `α(Y) ∧ φ(X) -> •φ'(X)` // by (9) and (10)
1. `∀ Y . α(Y) ∧ φ(X) -> •φ'(X)` // by (11)
1. `(∃ Y . α(Y)) ∧ φ(X) -> •φ'(X)` // by (12), FOL reasoning, and Prop 5.12

**Note:** `φ'(X)` will be `⊥` if the unification fails.


