Algorithm for applying one rule to a pattern
============================================

**Input:** `φ(X)`, `∀ Y .α(Y) -> •β(Y)`

We assume `α(Y) = tα(Y) ∧ pα(Y)` such that:

- `tα(Y)` is a pattern formed only with constructors, subsort injections,
  domain values, and variables, and therefore functional.
- `pα(Y)` is a predicate

We also assume `φ(X) = tφ(X) ∧ pφ(X)` such that:

- `tφ(X)` is a function-like pattern
- `pφ(X)` is a predicate

Note: • is "strong next" in this document

**Output:** a pattern `φ'(X)` satisfying the same assumptions we put on
  `φ(X)` such that
```
φ(X) ∧ (∃ Y . α(Y)) -> •φ'(X)
```

**Algorithm:**

1. Call *And Simplification* on `tφ(X) ∧ tα(Y)` to obtain a function-like
   pattern `t(X,Y)`, a substitution `subst(X,Y)`, and a predicate `p(X,Y)`.

   Note: *And Simplification* can be performed such that `t(X,Y) = tα(Y)`

   Note: `subst(X,Y)` is meant to substitute (all) variables from `Y`
   with terms (only) containing variables from `X`. If there are equalities
   substituting variables from `X`, they should be considered as part of the
   predicate `p(X,Y)`.

   Then, `α(Y) ∧ φ(X) = tα(Y) ∧ subst(X,Y) ∧ p(X,Y) ∧ pα(Y) ∧ pφ(X)`

   Note: `\ceil(α(Y) ∧ φ(X)) = subst(X,Y) ∧ p(X,Y) ∧ pα(Y) ∧ pφ(X)`
   (by Prop 5.12 and \ceil(t) = \top)

   Note: if the unification fails, then `p(X,Y)` will be `⊥`

   Note: We assume that `subst(X,Y)` assigns a value to each variable in `Y`.
   If that does not happen, then the algorithm will fail.
2. Call *Simplification Procedure* on
   `∃ Y . (subst(X,Y) ∧ p(X,Y) ∧ pα(Y) ∧ pφ(X) ∧ β(Y))`
   and obtain a pattern `φ'(X)` *without existential quantification*.
3. Return `φ'(X)`

**Proof Object Generation.**

1.  `α(Y) -> •β(Y)` // by axiom
2.  `α(Y) ∧ \ceil(α(Y) ∧ φ(X)) -> (•β(Y)) ∧ \ceil(α(Y) ∧ φ(X))`
    // by (1) and propositional reasoning
3.  `α(Y) ∧ \ceil(α(Y) ∧ φ(X)) = α(Y) ∧ φ(X)` // by ML paper Prop. 5.24
4.  `α(Y) ∧ φ(X) -> (•β(Y)) ∧ \ceil(α(Y) ∧ φ(X))` // by (2) and (3)
5.  `α(Y) ∧ φ(X) =  tα(Y) ∧ subst(X,Y) ∧ p(X,Y) ∧ pα(Y) ∧ pφ(X)`
    // by Unification Procedure
6.  `α(Y) ∧ φ(X) -> subst(X,Y) ∧ p(X,Y) ∧ pα(Y) ∧ pφ(X) ∧ •β(Y)` // by (4) (5)
7.  `α(Y) ∧ φ(X) -> ∃ Y . (subst(X,Y) ∧ p(X,Y) ∧ pα(Y) ∧ pφ(X) ∧ •β(Y))`
    // by (7) FOL reasoning
8.  `α(Y) ∧ φ(X) -> •(∃ Y . (subst(X,Y) ∧ p(X,Y) ∧ pα(Y) ∧ pφ(X) ∧ •β(Y)))`
    // by (8) Propagation
9.  `∃ Y . (subst(X,Y) ∧ p(X,Y) ∧ pα(Y) ∧ pφ(X) ∧ •β(Y)) = φ'(X)`
    // by (recursively calling) *Basic Simplification*
10. `α(Y) ∧ φ(X) -> •φ'(X)` // by (9) and (10)
11. `∀ Y . α(Y) ∧ φ(X) -> •φ'(X)` // by (11)
12. `(∃ Y . α(Y)) ∧ φ(X) -> •φ'(X)` // by (12), FOL reasoning, and Prop 5.12

**Note:** `φ'(X)` will be `⊥` if the unification fails.


