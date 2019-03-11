Equality Axiom Configuration Splitting
======================================

Background
----------

Functions are defined through axioms of the type `∀ Z . α(Z) = β(Z)`. The same
axioms are used for `ceil` evaluation and for simplifying functions without
evaluating them.

These axioms are interpreted in a directional way, i.e. if we find `α(Z)`,
we can transform it into `β(Z)`.

In order to apply this axiom to a pattern `φ(X)`, let us first take an example:
if the axiom is `sgn(z) = -1 if z < 0`, which means that `α(z) = sgn(z) ∧ z<0`
and `β(Z) = -1`, and if `φ(x)=sgn(x+1)`, then we will try to find an unifier
for `α(z)` and `φ(x)`. It's easy to identify a substitution `S(x,z) = [z = x+1]`
which must be part5 of this unifier, but `z<0` must also be part of it, so our
unifier will be a predicate `P(x, z) = [z = x+1] ∧ z<0` (check the "Details"
section to see why).

In general, the unifier will be in the form of a predicate `P(X, Z)`, which can
be `⊥`, such that
```
P(X, Z) ∧ φ(X) = P(X, Z) ∧ α(Z)
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

Details
-------

### Unification

When matching two terms, `t(X)` and `s(Z)`, one normally gets a substitution
`S(X, Z)`. As an example, when matching `f(sigma(x1), tau(x2))` with
`f(y1, tau(y2))` one may get `[y1=sigma(x1), y2=x2]`.

In some cases, this substitution may be accompanied by a predicate `P(X, Z)`,
e.g. when matching `f(g(x1), x2)` with `f(a, y1)` one will get a predicate
`g(x1)=a` and a substitution `y1=x2`.

However, let us note that, unlike when rewriting, we usually don't want to
use the most general unifier. As an example, let's say that we want to define
`f(z)` with these axioms:
```
f(z) = sin(z) if z < 0
f(z) = cos(z) if z >= 0
```
and let's say that we want to apply the first of these equations to `f(x)`.
The most general unifier is
```
⌈f(x) ∧ f(z) ∧ z < 0⌉

    -- since f is a function
  = ⌈f(x)⌉ ∧ (f(x) == f(z)) ∧ z < 0

    -- since f is actually functional
  = (f(x) == f(z)) ∧ z < 0
```
from which we can't infer a substitution for `z` since `(f(x) == f(z)) ∧ z < 0`
has an infinity of solutions.

At the opposite end of the spectrum, `⊥` is always a unifier, but we usually
want something better, since we do want to apply the axiom if possible.

So we search for a unifier which lies somewhere between `⊥` and the most
general unifier. For this, we match the structure of the two terms as much as
possible, identifying identical node types (e.g. both nodes are `application`s
of the same head, both nodes are `and` and so on), and we have a few special
cases for handling different node types (e.g. a variable vs a functional term
becomes a substitution).

This unifier consists of a predicate `Q(X, Z)` and a substitution `S(X,Z)`.
But, since a substitution is a predicate, we can say that we end up with a
predicate `P(X, Z)=Q(X, Z) ∧ S(X, Z)`.

As an example, if we try to apply the axiom
`if (true, z1, Z2)` to `if(x<2, 10, 20)`, we will get
`S(x, z1, z2) = [z1=10, z2=20]` and `Q(X, Y) = (true == x<2)`.

Now, when we generalize this to random formulas, `φ(X)` and `α(Z)`, we still
get a predicate `P(X, Z)` as a unifier, with `⊥ ⊆ P(X, Z) ⊆ ⌈φ(X) ∧ α(Z)⌉`.
If, say, we have terms `t(X)` and `s(Z)` with predicates `Q(X)` and `R(Z)`
such that `φ(X) = t(X) ∧ Q(X)` and `α(Z) = s(Z) ∧ R(Z)`, and `P'(X, Z)` is
a unifier for `t(X)` and `s(Z)`, then we can take `P(X, Z)` to be
`Q(X) ∧ P'(X, Z) ∧ R(Z)`.

As an example, if we try to apply `sgn(z) = -1 if z < 0`
(so `α(z) = sgn(z) ∧ z<0`) to `φ(x) = sgn(x+1) ∧ x>-5`, we would have:
```
t(x) = sgn(x+1)
s(z) = sgn(z)
Q(x) = x>-5
R(z) = z<0
```
And we would compute:
```
P'(x, z) = S(x, z) = [z=x+1]
P(x, z) = x>-5 ∧ z<0 ∧ [z=x+1]
```

### Removing exists

Assuming that `P(X, Z)` contains a substitution `S(X, Z)` which covers all
variables in `Z`, then, for all formulas `ψ(Z)`, there is another formula
`ψ'(X)` and a predicate `P'(X)`, which we get through substitution, such that:

```
∃ Z . P(X, Z) ∧ ψ(Z)

  -- apply the substitution
  = ∃ Z . P'(X) ∧ ψ'(X) ∧ S(X, Z)

  -- ∃ Z . a ∧ b = a ∧ ∃ Z . b if Z does not occur free in a
  = P'(X) ∧ ψ'(X) ∧ ∃ Z . S(X, Z)

  -- ∃ Z . Z = a is always top if a is functional, and we assume that
  -- patterns used in substitutions are relatively functional.
  = P'(X) ∧ ψ'(X)
```

Continuing the `sgn(x+1)` example above, if
```
P(x, z) = x>-5 ∧ z<0 ∧ [z=x+1]
```
then we would have
```
P'(x) = x>-5 ∧ z<0
ψ'(x) = ψ(x+1)
```
So we can do this:
```
∃ z . P(x, z) ∧ ψ(z)

  -- term expansion
  = ∃ z . x>-5 ∧ z<0 ∧ [z=x+1] ∧ ψ(z)

  -- apply substitution
  = ∃ z . x>-5 ∧ x+1<0 ∧ [z=x+1] ∧ ψ(x+1)

  -- ∃ Z . a ∧ b = a ∧ ∃ Z . b if Z does not occur free in a
  = x>-5 ∧ x+1<0 ∧ ψ(x+1) ∧ (∃ z . [z=x+1])

  -- (∃ z . [z=x+1]) is top
  = x>-5 ∧ x+1<0 ∧ ψ(x+1)

  = P'(x) ∧ ψ'(x)
```

Problem
-------

Above I described how we can transform parts of a pattern
(`∃ Z . P(X, Z) ∧ α(Z)` being transformed to `∃ Z . P(X, Z) ∧ β(Z)`). The
main question is how to transform the entire pattern with, e.g., a function
definition.

Solution
--------

Let us assume that we have several axioms `∀ Zi . αi(Zi) = βi(Zi)` which we
think we should apply together (e.g. they form a function definition).

We identify `Pi(X, Zi)` such that
```
(∃ Zi . Pi(X, Zi) ∧ φ(X)) = (∃ Zi . Pi(X, Zi) ∧ αi(Zi)).
```
Let
```
Qi(X) = (¬ ∃ Z1 . P1(X, Z1)) ∧ ... ∧ (¬ ∃ Zi . Pi(X, Zi))
```

Note that, if all `Pi(X, Zi)` contain a substitution for all variables in `Zi`,
then `Qi(X)` and `∃ Zi . P1(X, Zi) ∧ β1(Zi)` can be reduced to formulas without
`∃ Zi`. Also,


Then we evaluate `φ(X)` as follows:
```
φ(X)

    --| a = (a ∧ b) ∨ (a ∧ ¬b)
  = (φ(X) ∧ ∃ Z1 . P1(X, Z1)) ∨ (φ(X) ∧ ¬ ∃ Z1 . P1(X, Z1))

    --| Q1's definition
  = (φ(X) ∧ ∃ Z1 . P1(X, Z1)) ∨ (φ(X) ∧ Q1(X))

    --| α1(Z1) = β1(Z1)
  = (∃ Z1 . P1(X, Z1) ∧ β1(Z1)) ∨ (φ(X) ∧ Q1(X))

    --| a = (a ∧ b) ∨ (a ∧ ¬b)
  = (∃ Z1 . P1(X, Z1) ∧ β1(Z1))
    ∨ (∃ Z2 . P2(X, Z2) ∧ β2(Z2) ∧ Q1(X))
    ∨ (φ(X) ∧ Q1(X)) ∧ (¬ ∃ Z2 . P2(X, Z2)))

    --| Q2's definition
  = (∃ Z1 . P1(X, Z1) ∧ β1(Z1))
    ∨ (∃ Z2 . P2(X, Z2) ∧ β2(Z2) ∧ Q1(X))
    ∨ (φ(X) ∧ Q2(X))
...
  = (∃ Z1 . P1(X, Z1) ∧ β1(Z1))
    ∨ (∃ Z2 . P2(X, Z2) ∧ β2(Z2) ∧ Q1(X))
    ...
    ∨ (∃ Zn . Pn(X, Zn) ∧ βn(Zn) ∧ Qn-1(X))
    ∨ (φ(X) ∧ Qn(X))
```

At the end, we usually expect that `⌈φ(X) ∧ Qn(X)⌉ = ⊥`. Currently
we only check whether `Qn(X) = ⊥`, but we may want to do more in the future.