Using a rule to advance a one-path reachability proof
=====================================================

This document describes how to transform a given a one-step reachability goal
by advancing it using a given rewrite axiom.

This document *does not describe* how to select an axiom to be used for
advancing the goal.


Problem statement
-----------------

Consider the following "one-path" reachability goal

```
∀ X . φ(X) → ◆ ∃ Y . ψ(X, Y)
```
where `X` and `Y` are sets of variables and ◆ denotes "strong-eventually"

Consider also the axiom

`∀ Z . α(Z) → ⚪ β(Z)`.

where ⚪  denotes "strong-next".

The steps below show how the given goal is transformed by "applying" the 
given axiom.

Unrolling "strong-eventually"
------------------------------

Let `Δ = ν f . ⚪ f` denote the formula for diverging computation.
Then,  for any formula ψ:

- `◆ ψ = ◇ ψ ∨ Δ` by the definition of "strong eventually"
- `    = ψ ∨ ⚪ ◇ ψ ∨ Δ` by unrolling `◆`
- `    = ψ ∨ ⚪ ◇ ψ ∨ ⚪ Δ` by unrolling `Δ`
- `    = ψ ∨ ⚪ (◇ ψ ∨ Δ)`
  because `⚪` commutes with `∨` 
- `    = ψ ∨ ⚪ ◆ ψ`


Therefore proving
```
∀ X . φ(X) → ◆ ∃ Y . ψ(X, Y)
```
is equivalent to proving
```
∀ X . φ(X) →  ∃ Y . ψ(X, Y) ∨ ⚪ ◆ ∃ Y . ψ(X, Y)`
```

We can now move `∃ Y . ψ(X, Y)` to the right of the implication,
and (assuming law of excluded middle) we obtain the equivalent:
```
∀ X . φ(X) ∧ ¬∃ Y . ψ(X, Y) →  ⚪ ◆ ∃ Y . ψ(X, Y)`
```

Applying the axiom `∀ Z . α(Z) → ⚪ β(Z)`
------------------------------------------

In the following let `Φ(X) = φ(X) ∧ ¬∃ Y . ψ(X, Y)`
and `Ψ(X) = ◆ ∃ Y . ψ(X, Y)`
 

We can now split the original goal onto `∃ Y. α(Y)` to obtain
the equivalent goal:

```
(∀ X . Φ(X) ∧ (∃ Z. α(Z)) → ⚪ Ψ(X))
∧
(∀ X . Φ(X) ∧ (¬ ∃ Z. α(Z)) → ⚪ Ψ(X))
```

Now we know, from the basic symbolic execution algorithm that
```
Φ(X) ∧ (∃ Y .α(Y)) → ⚪ Φ'(X)    (Step)
```
for some `Φ'` determined by the algorithm.

It is then sound to replace the first conjunct in the goal above with
```
∀ X . Φ'(X) → Ψ(X)
```

That is indeed so, because

`∀ X . Φ'(X) → Ψ(X)` implies `∀ X . ⚪ Φ'(X) → ⚪ Ψ(X)`
which, by using `(Step)` and implication transitivity, implies that
```
Φ(X) ∧ (∃ Y . α(Y)) → ⚪ Ψ(X)
```


Therefore, it is sound to replace the original goal with 
```
(∀ X . Φ'(X) → ◆ ∃ Y . ψ(X, Y))
∧
(∀ X . Φ(X) ∧ (¬ ∃ Z. α(Z)) → ⚪ ◆ ∃ Y . ψ(X, Y))
```

Examples of using the above procedure 
-------------------------------------

When applying an axiom on a symbolic configuration new constraints may be
introduced on symbolic variables, coming from side conditions, or directly
from the unification process.

### Example (from side conditions)

Consider proving that
```
forall A:Int . 3 / A -> \diamond \exists B:Int . B
```

using axiom
```
forall X:Int, Y:Int .  (Y =/=Int 0 = true) \and X / Y -> \next X /Int Y
```

Then the goal will simplify to
```
(\forall A:Int . 3 /Int A \and (A =/=Int 0 = true)-> \diamond \exists B:Int . B)
\and
(\forall A:Int . 3 / A \and \not (A =/=Int 0 = true) -> \next \diamond \exists B:Int . B
```

The first conjunct can be discharged immediately, leaving the second
one as a goal.
```
(\forall A:Int . 3 / A \and \not (A =/=Int 0 = true) -> \next \diamond \exists B:Int . B
```


### Example (from unification)

Consider proving goal
```
\forall A:Int . if A <Int 0 then -1 else 1 -> \diamond (-1 \or 1)`

using axioms
```
\forall E1:Exp, E2:Exp . if true then E1 else E2 -> \next E1
```
and
```
\forall E1:Exp, E2:Exp . if false then E1 else E2 -> \next E2
```

Then, by using the first axiom, the goal will simplify to
```
(\forall A:Int . -1 \and A <Int 0 = true -> \diamond (-1 \or 1))
\and
(\forall A:Int . if A <Int 0 then -1 else 1 \and \not(A <Int 0 = true) -> \next\diamond (-1 \or 1))
```

The first conjunct can be discharged immediately. Also, using that `true` and
`false` are the only constructors for `Bool`, `\not(A <Int 0 = true)` can
be simplified to `A <Int 0 = false`, making the goal:
```
(\forall A:Int . if A <Int 0 then -1 else 1 \and A <Int 0 = false -> \next\diamond (-1 \or 1))
```

By applying next the "else" axiom,  we obtain the goal:
```
(\forall A:Int . 1 \and A <Int 0 = false -> \diamond (-1 \or 1))
\and
(\forall A:Int . if A <Int 0 then -1 else 1 \and \not(A <Int 0 = true)  \and \not(A <Int 0 = false)-> \next\diamond (-1 \or 1))
```

Now both conjuncts are discharged immediately
(the first because it matches the conclusion while the second because
its premise has became `false`).

