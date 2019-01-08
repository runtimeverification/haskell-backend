Using a rule to advance a one-path reachability proof
=====================================================

This document describes how to transform a given a one-step reachability goal
by advancing it using a given rewrite axiom.

This document *does not describe* how to select an axiom to be used for
advancing the goal.

Background
----------

Unless otherwise specified, we assume all pattern variables used in this
document to be _extended function-like patterns_, that is patterns which
can be written as `t ∧ p` where the interpretation of `t` contains at most one
element and `p` is a predicate.

_Extended constructor patterns_ will be those extended function-like patterns
for which `t` is a functional term, composed out of constructor-like symbols
and variables.

### And-Not-Exists Simplification
---------------------------------

We will use the algorithm for simplifying patterns of the form
`φ(X) ∧ ¬∃ Y . ψ(X, Y)`
to a extended function-like pattern described in
[Configuration Splitting Simplification](2018-11-08-Configuration-Splitting-Simplification.md).

This algorithm will be named `AndNotExistsSimplification` in the sequel.

Note: the process is quite similar to unification, and the result is either
`φ(X)`, if `φ(X)` and `ψ(X, Y)` are not unifiable, or
`φ(X) ∧ p(X)`, where `p(X)` is the negation of the predicate of `ψ(X, Y)`
on which the unifying substitution of `φ(X)` and `ψ(X, Y)` was applied, if
the two are unifiable.


Algorithm
---------

Consider the following "one-path" reachability goal

```
∀ X . φ(X) → ◇w ∃ Y . ψ(X, Y)
```
where `X` and `Y` are sets of variables and `◇w` denotes "weak-eventually"

Consider also the axiom

`∀ Z . α(Z) → •β(Z)`.

where `•` denotes "strong-next" (`α(Z)` is an extended constructor pattern).

The steps below show how the given goal is transformed by "applying" the
given axiom.


### Unrolling "weak-eventually"

Let `Δ = ν f . •f` denote the formula for diverging computation.
Then,  for any formula ψ:

- `◇w ψ = ◇ ψ ∨ Δ` by the definition of "weak eventually"
- `    = ψ ∨ •◇ ψ ∨ Δ` by unrolling `◇`
- `    = ψ ∨ •◇ ψ ∨ •Δ` by unrolling `Δ`
- `    = ψ ∨ •(◇ ψ ∨ Δ)`
  because `•` commutes with `∨`
- `    = ψ ∨ •◇w ψ`


Therefore proving
```
∀ X . φ(X) → ◇w ∃ Y . ψ(X, Y)
```
is equivalent to proving
```
∀ X . φ(X) →  ∃ Y . ψ(X, Y) ∨ •◇w ∃ Y . ψ(X, Y)`
```

We can now move `∃ Y . ψ(X, Y)` to the left of the implication,
and (assuming law of excluded middle) we obtain the equivalent:
```
∀ X . φ(X) ∧ ¬∃ Y . ψ(X, Y) →  •◇w ∃ Y . ψ(X, Y)`
```


### Applying the axiom `∀ Z . α(Z) → •β(Z)`

In the following let `Ψ(X) = ◇w ∃ Y . ψ(X, Y)` and let `Φ(X)` be the extended
function-like pattern obtained from applying the
`AndNotExistsSimplification` algorithm to `φ(X) ∧ ¬∃ Y . ψ(X, Y)`.

We can now split the original goal on `∃ Y. α(Y)` to obtain
the equivalent goal:

```
(∀ X . Φ(X) ∧ (∃ Z. α(Z)) → •Ψ(X))
∧
(∀ X . Φ(X) ∧ (¬ ∃ Z. α(Z)) → •Ψ(X))
```

Now we know, from the [basic symbolic execution algorithm](2018-11-08-Applying-Axioms.md)
that
```
Φ(X) ∧ (∃ Y .α(Y)) → •Φ'(X)    (Step)
```
for some `Φ'` determined by the algorithm.

It is then sound to replace the first conjunct in the goal above with
```
∀ X . Φ'(X) → Ψ(X)
```

That is indeed so, because

`∀ X . Φ'(X) → Ψ(X)` implies `∀ X . •Φ'(X) → •Ψ(X)`
which, by using `(Step)` and implication transitivity, implies that
```
Φ(X) ∧ (∃ Y . α(Y)) → •Ψ(X)
```

Moreover, we can apply the `AndNotExistsSimplification` algorithm on
`Φ(X) ∧ (¬ ∃ Z. α(Z))` to obtain an extended function-like pattern `Φα(X)`.


Therefore, it is sound to replace the original goal with
```
(∀ X . Φ'(X) → ◇w ∃ Y . ψ(X, Y))
∧
(∀ X . Φα(X) → •◇w ∃ Y . ψ(X, Y))
```

The process of applying an axiom can then be restarted on the second conjunct,
using a different axiom, until `Φα(X)` becomes `⊥`.

Examples of using the above procedure
-------------------------------------

When applying an axiom on a symbolic configuration new constraints may be
introduced on symbolic variables, coming from side conditions, or directly
from the unification process.

### Example (from side conditions)

Consider proving that
```
∀ A:Int . 3 / A -> ◇w ∃ B:Int . B
```

using axiom
```
∀ X:Int, Y:Int .  (Y =/=Int 0 = true) ∧ X / Y -> • X /Int Y
```

Then the goal will simplify to
```
(∀ A:Int . 3 /Int A ∧ (A =/=Int 0 = true)-> ◇w ∃ B:Int . B)
∧
(∀ A:Int . 3 / A ∧ ¬ (A =/=Int 0 = true) -> • ◇w ∃ B:Int . B)
```

The first conjunct can be discharged immediately, leaving the second
one as a goal.
```
(∀ A:Int . 3 / A ∧ ¬ (A =/=Int 0 = true) -> • ◇w ∃ B:Int . B
```

### Example (from unification)

Consider proving the goal
```
∀ A:Int . if A <Int 0 then -1 else 1 -> ◇w (∃ B:Int . B = -1 ∨  B = 1)
```

using axioms
```
∀ E1:Exp, E2:Exp . if true then E1 else E2 -> • E1
```
and
```
∀ E1:Exp, E2:Exp . if false then E1 else E2 -> • E2
```

First, we unroll `◇w` to get
```
∀ A:Int . if A <Int 0 then -1 else 1 ∧ ¬(∃ B:Int . B = -1 ∨  B = 1) -> •◇w (∃ B:Int . B = -1 ∨  B = 1)
```

Now, since the `if` construct is not an integer, this simplifies to
```
∀ A:Int . if A <Int 0 then -1 else 1 -> •◇w (∃ B:Int . B = -1 ∨  B = 1)
```


Then, by using the first axiom, the goal will simplify to
```
(∀ A:Int . -1 ∧ A <Int 0 = true -> ◇w (∃ B:Int . B = -1 ∨  B = 1))
∧
(∀ A:Int . if A <Int 0 then -1 else 1 ∧ ¬(A <Int 0 = true) -> •◇w (∃ B:Int . B = -1 ∨  B = 1))
```

The first conjunct can be discharged immediately. Also, using that `true` and
`false` are the only constructors for `Bool`, `¬(A <Int 0 = true)` can
be simplified to `A <Int 0 = false`, making the goal:
```
(∀ A:Int . if A <Int 0 then -1 else 1 ∧ A <Int 0 = false -> •◇w (∃ B:Int . B = -1 ∨  B = 1))
```

By applying next the "else" axiom,  we obtain the goal:
```
(∀ A:Int . 1 ∧ A <Int 0 = false -> ◇w (∃ B:Int . B = -1 ∨  B = 1))
∧
(∀ A:Int . if A <Int 0 then -1 else 1 ∧ ¬(A <Int 0 = true)  ∧ ¬(A <Int 0 = false)-> •◇w (∃ B:Int . B = -1 ∨  B = 1))
```

Now both conjuncts are discharged immediately
(the first because it matches the conclusion while the second because
its premise has became `false`).

