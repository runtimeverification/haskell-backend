Splitting configurations upon new constraints on symbolic variables
===================================================================

Background
----------

When applying an axiom on a symbolic configuration new constraints may be
introduced on symbolic variables, coming from side conditions, or directly
from the unification process.

### Example (from side conditions)

Consider rewriting term `3 / A:Int` using

`rule X:Int / Y:Int => X /Int Y requires Y =/=Int 0`
which would be written as
`Y =/= 0 = true ∧ X:Int / Y:Int => X /Int Y`

Then `3 / A:Int ∧ (Y =/=Int 0 = true ∧ X:Int / Y:Int)` will simplify to
```
3 / A:Int ∧ (X:Int = 3 ∧ Y:Int = A:Int)
          ∧ (A:Int =/=Int 0) = true
```
which is satisfiable, but not `T`.

### Example (from unification)

Consider rewriting term `if A:Int <Int 0 then -1 else 1` using

`rule if true then E1:Exp else E2:Exp => E1`

Then `if A:Int <Int 0 then -1 else 1 ∧ if true then E1:Exp else E2:Exp` will
simplify to
```
if A:Int <Int 0 then -1 else 1 ∧ (E1:Exp = -1 ∧ E2:Exp = 1)
                               ∧ A:Int <Int 0 = true
```
which is satisfiable, but not `T`.

Problem
-------

Consider the following "one-path" reachability problem

```
∀ X . φ(X) -> ◇ ∃ Y . ψ(X, Y)
```
where `X` and `Y` are sets of variables.

### Reduction to proving a ○ implication

By unrolling ◇ we obtain:
```
∀ X . φ(X) ->  ∃ Y . ψ(X, Y) ∨ ○ ◇ ∃ Y . ψ(X, Y)
```

We can now move `∃ Y . ψ(X, Y)` to the right of the implication,
and (assuming law of excluded middle) we obtain the equivalent:
```
(∀ X . (φ(X) ∧ ¬∃ Y . ψ(X, Y)) -> ○ ◇ ∃ Y . ψ(X, Y))
```

#### Basic Symbolic Execution

**Input:** `φ(X)`, `∀ Y .α(Y) -> ○ β(Y)`

**Output:** a pattern `φ'(X)` and satisfying the same assumptions we put on
  `φ(X)` such that
```
φ(X) ∧ (∃ Y . α(Y)) -> ○ φ'(X)
```

**Algorithm:**

1. Call *And Simplification* on `φ(X) ∧ α(Y)` to obtain functional
   pattern  `t(X,Y)`, and substitution `subst(X,Y)` and predicate `p(X,Y)`.
 
   Note: if the unification fails, then `p(X,Y)` will be `⊥`

   Note: `\ceil(α(Y) ∧ φ(X)) = subst(X,Y) ∧ p(X,Y)`
   (by Prop 5.12 and \ceil(t) = \top)
1. Call *Simplification Procedure* on `∃ Y . (subst(X,Y) ∧ p(X,Y) ∧ β(Y))`
   and obtain a pattern `φ'(X)` *without existential quantification*.
1. Return `φ'(X)`

**Proof Object Generation.**

1. `α(Y) -> ○ β(Y)` // by axiom
1. `α(Y) ∧ \ceil(α(Y) ∧ φ(X)) -> (○ β(Y)) ∧ \ceil(α(Y) ∧ φ(X))` // by (1) and propositional reasoning
1. `α(Y) ∧ \ceil(α(Y) ∧ φ(X)) = α(Y) ∧ φ(X)` // by ML paper Prop. 5.24
1. `α(Y) ∧ φ(X) -> (○ β(Y)) ∧ \ceil(α(Y) ∧ φ(X))` // by (2) and (3)
1. `α(Y) ∧ φ(X) = t(X,Y) ∧ subst(X,Y) ∧ p(X,Y)` // by Unification Procedure
1. `α(Y) ∧ φ(X) -> subst(X,Y) ∧ p(X,Y) ∧ ○ β(Y)` // by (4) (5)
1. `α(Y) ∧ φ(X) -> ∃ Y . (subst(X,Y) ∧ p(X,Y) ∧ ○ β(Y))` // by (7) FOL reasoning
1. `α(Y) ∧ φ(X) -> ○ (∃ v . (β(Y) ∧ subst(X,Y) ∧ p(X,Y)))` // by (8) Propagation
1. `∃ Y . (β(Y) ∧ subst(X,Y) ∧ p(X,Y)) = φ'(X)` // by (recursively calling) *Basic Simplification*
1. `α(Y) ∧ φ(X) -> ○ φ'(X)` // by (9) and (10)
1. `∀ Y . α(Y) ∧ φ(X) -> ○ φ'(X)` // by (11)
1. `(∃ Y . α(Y)) ∧ φ(X) -> ○ φ'(X)` // by (12), FOL reasoning, and Prop 5.12

**Note:** `φ'(X)` will be `⊥` if the unification fails.

### Proving `∀ X . φ(X) -> ○ ψ(X)`

We use just `ψ(X)` for simplicity.  However, note that `ψ(X)` could be
of the form `◇ ∃ Y . ψ(X, Y)` encountered above.

Now, say the definition contains an axiom of the form
`∀ Y . α(Y) -> ○ β(Y)`.

We can now split the original goal onto `∃ Y. α(Y)` to obtain
the equivalent goal:

```
(∀ X . φ(X) ∧ (∃ Y. α(Y)) -> ○ ψ(X))
∧
(∀ X . φ(X) ∧ (¬ ∃ Y. α(Y)) -> ○ ψ(X))
```

Now we know, from the basic symbolic execution paragraph above, that
```
φ(X) ∧ (∃ Y . α(Y)) -> ○ φ'(X)    (Step)
```
for some `φ'` determined by the algorithm.

It is then sound to replace the first conjunct in the goal above with
`∀ X . φ'(X) -> ψ(X)`.  That is indeed so, because

`∀ X . φ'(X) -> ψ(X)` implies `∀ X . ○ φ'(X) -> ○ ψ(X)` which,
by using `(Step)` and implication transitivity, implies that
```
φ(X) ∧ (∃ Y . α(Y)) -> ○ ψ(X)
```
 
Decision: Reduce premise when unrolling `◇ `
--------------------------------------------
That is, replace the goal
```
∀ X . φ(X) -> ◇ ∃ Y . ψ(X, Y)
```
by the goal
```
(∀ X . (φ(X) ∧ ¬∃ Y . ψ(X, Y)) -> ○ ◇ ∃ Y . ψ(X, Y))
```

Decision: Split on matching when using rule to advance one-path proof
---------------------------------------------------------------------
That is, replace the goal
```
∀ X . φ(X) -> ○ ψ(X)
```
by the goal(s)
```
(∀ X . φ'(X) -> ψ(X))
∧
(∀ X . φ(X) ∧ (¬ ∃ Y. α(Y)) -> ○ ψ(X))
```
where `φ'(X)` is obtained through Basic Symbolic Execution from
`φ(X)` and `∀ Y .α(Y) -> ○ β(Y)`.
