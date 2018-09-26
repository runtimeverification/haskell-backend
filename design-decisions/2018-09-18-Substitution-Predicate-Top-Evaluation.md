Substitution-Predicate Top Evaluation
=====================================

Problem description
-------------------

At times, when evaluating a pattern `φ` inside a context `C[φ]`, we may get
`ψ ∧ P`, where `P` is a predicate (with or without a substitution). We can
then evaluate `C[φ]` to either
1. `C[ψ ∧ P]`, or
1. `(P ∧ C[ψ]) ∨ (¬P ∧ C[⊥])`
   (see the proof-ish stuff below for why this is the case).

Also, at times, we may want to split a pattern into two based on a predicate,
say, when applying the rules for a function's definition. We then want to write
`C=(P ∧ C) ∨ (¬P ∧ C)` and we want to be able to use this split effectively,
both when rewriting and when simplifying the formulas.

In particular, when we have a formula `P ∧ C[φ])` we may want to be able
to use `P` when evaluating `φ` (say, we may want to know if we can apply a
function).

Motivation
----------

Splitting the formula at the top based on predicates found inside a context
means that evaluating `not`, `iff`, and other difficult patterns becomes easier.

Using formulas from the top inside contexts allows us to do more efficient
branch prunning, and allows us to know when it is safe to evaluate a symbolic
function (always evaluating can lead to infinite loops, but evaluating when
the function condition is true may work).

In general, having predicates only at the top prevents us from having
contradictory cases in different places of the formula (e.g. `x=0` vs `x=1`),
with no practical way of detecting the contradiction.

Splitting the formula at the top with `C=(P ∧ C) ∨ (¬P ∧ C)` may be another way
of assisting with function evaluation.

Splitting at the top when inside a context.
-------------------------------------------

Currently, the evaluation of a formula `φ` inside a context `C[φ]` is
represented as
```
(term ∧ predicate ∧ substitution) ∨ (term ∧ predicate ∧ substitution) ∨ ...
```
Whenever one of the and-ed items in `term ∧ predicate ∧ substitution`
(including the term) becomes bottom, we evaluate the entire and to bottom
and remove it from the or formula.

However, we may also give it a different meaning: we could work with
`(term, predicate ∧ substitution)` pairs, where the
`predicate ∧ substitution` element refers to a split which may be done
at the current evaluation level (`φ`) or any level above it in the context `C`.
This means that having a bottom `term` does not force the entire pair to bottom,
but a bottom predicate does, since its branch will be removed when doing the
actual split.

Note that at the splitting level, the `(term, predicate ∧ substitution)` pair
has the original meaning of `(term ∧ predicate ∧ substitution)`.

Function evaluation
-------------------

Say we have a function defined as
```
f(x)=v1 if P1
f(x)=v2 if P2
...
f(x)=vn if Pn
```

Then, when evaluating f inside a context `C[f(y)]` we do this:
```
C[f(y)]
    = (P1 ∧ C[f(y)]) ∨ (¬P1 ∧ C[f(y)])
    = (P1 ∧ C[f(y)])
        ∨ (¬P1 ∧ P2 ∧ C[f(y)])
        ∨ (¬P1 ∧ ¬P2 ∧ C[f(y)])
    ...
    = (P1 ∧ C[f(y)])
        ∨ (¬P1 ∧ P2 ∧ C[f(y)])
        ∨ (¬P1 ∧ ¬P2 ∧ P3 ∧ C[f(y)])
        ...
        ∨ (¬P1 ∧ ¬P2 ... ∧ ¬Pn-1 ∧ Pn ∧ C[f(y)])
        ∨ (¬P1 ∧ ¬P2 ... ∧ ¬Pn-1 ∧ ¬Pn ∧ C[f(y)])
```
which, assuming confluence or disjoint predicates, and using
`P ∧ C[φ] = P ∧ C[φ ∧ P])` (see the proof-ish section) and `f(y)=⊥` if no
function definition branch is matched (i.e. `¬P1 ∧ ¬P2 ... ∧ ¬Pn-1 ∧ ¬Pn`,
probabily needs a separate axiom), becomes
```
C[f(y)]
    = (P1 ∧ C[f(y) ∧ P1])
        ∨ (P2 ∧ C[f(y) ∧ P2])
        ∨ (P3 ∧ C[f(y) ∧ P3])
        ...
        ∨ (Pn ∧ C[f(y) ∧ Pn])
        ∨ (¬P1 ∧ ¬P2 ... ∧ ¬Pn-1 ∧ ¬Pn ∧ C[⊥])
    = (P1 ∧ C[v1])
        ∨ (P2 ∧ C[v2])
        ∨ (P3 ∧ C[v3])
        ...
        ∨ (Pn ∧ C[vn])
        ∨ (¬P1 ∧ ¬P2 ... ∧ ¬Pn-1 ∧ ¬Pn ∧ C[⊥])
```

But, if we want to do bottom-up splitting, we can also evaluate it like this:
```
f(y)
    = (f(y) ∧ P1) ∨ (f(y) ∧ ¬P1)
    = (f(y) ∧ P1)
        ∨ (f(y) ∧ ¬P1 ∧ P2)
        ∨ (f(y) ∧ ¬P1 ∧ ¬P2)
    ...
    = (f(y) ∧ P1)
        ∨ (f(y) ∧ ¬P1 ∧ P2)
        ∨ (f(y) ∧ ¬P1 ∧ ¬P2 ∧ P3)
        ...
        ∨ (f(y) ∧ ¬P1 ∧ ¬P2 ... ∧ ¬Pn-1 ∧ Pn)
        ∨ (f(y) ∧ ¬P1 ∧ ¬P2 ... ∧ ¬Pn-1 ∧ ¬Pn)
```
By using confluence or disjoint predicates, this becomes
```
f(y)
    = (f(y) ∧ P1)
        ∨ (f(y) ∧ P2)
        ∨ (f(y) ∧ P3)
        ...
        ∨ (f(y) ∧ Pn)
        ∨ (f(y) ∧ ¬P1 ∧ ¬P2 ... ∧ ¬Pn-1 ∧ ¬Pn)
    = (v1 ∧ P1)
        ∨ (v2 ∧ P2)
        ∨ (v3 ∧ P3)
        ...
        ∨ (vn ∧ Pn)
        ∨ (⊥ ∧ ¬P1 ∧ ¬P2 ... ∧ ¬Pn-1 ∧ ¬Pn)
    = (v1 ∧ P1)
        ∨ (v2 ∧ P2)
        ∨ (v3 ∧ P3)
        ...
        ∨ (vn ∧ Pn)
```
When evaluating this inside the context, we have (assuming confluence, see
the proof-ish section for details)
```
C[f(y)]
    = C[(v1 ∧ P1) ∨ (v2 ∧ P2) ∨ (v3 ∧ P3) ... ∨ (vn ∧ Pn)]
    = (P1 ∧ C[v1])
        ∨ (P2 ∧ C[v2])
        ∨ (P3 ∧ C[v3])
        ...
        ∨ (Pn ∧ C[vn])])
        ∨ (¬P1 ∧ ¬P2 ∧ ... ∧ ¬Pn ∧ C[⊥])
```

This means that we are justified in representing the function evaluation
using the pair representation:
```
f(x) = (v1, P1 ∧ []) ∨ (v2, P2 ∧ []) ∨ ... ∨ (vn, Pn ∧ [])
        ∨ (⊥, ¬P1 ∧ ¬P2 ∧ ... ∧ ¬Pn ∧ [])
```

Proof-ish stuff
---------------

First, let us note that, if `P` is a predicate and `C` is a context, then
```
C[P] = (P ∧ C[T]) ∨ (¬P ∧ C[⊥])
```

Indeed, if `P` is `⊤`, then the equation becomes
```
C[⊤] = (⊤ ∧ C[⊤]) ∨ (¬⊤ ∧ C[⊥])
```
which is obviously true.

If `P` is `⊥` then the equation becomes
```
C[⊥] = (⊥ ∧ C[T]) ∨ (¬⊥ ∧ C[⊥])
```
which, again, is obviously true.

But then, we have
```
P ∧ C[φ ∧ P])
    = P ∧ ((P ∧ C[φ ∧ T]) ∨ (¬P ∧ C[φ ∧ ⊥]))
    = P ∧ ((P ∧ C[φ]) ∨ (¬P ∧ C[⊥]))
    = (P ∧ P ∧ C[φ]) ∨ (P ∧ ¬P ∧ C[⊥])
    = (P ∧ C[φ]) ∨ ⊥
    = P ∧ C[φ]
```
which gives us the formula we need for moving predicates (and substitutions,
since they are a special case of predicate) inside any contexts.

To generalize, we have
```
C[(φ1 ∧ P1) ∨ (φ2 ∧ P2) ∨ ... ∨ (φn ∧ Pn)]
    = (P1 ∧ (C[φ1 ∨ (φ2 ∧ P2) ∨ ... ∨ (φn ∧ Pn)]))
        ∨ (¬P1 ∧ (C[(φ2 ∧ P2) ∨ ... ∨ (φn ∧ Pn)]))
    = (P1 ∧ (C[φ1 ∨ (φ2 ∧ P2) ∨ ... ∨ (φn ∧ Pn)]))
        ∨ (¬P1 ∧ P2 ∧ (C[φ2 ∨ ... ∨ (φn ∧ Pn)]))
        ...
        ∨ (¬P1 ∧ ¬P2 ∧ ... ¬Pn-1 ∧ Pn ∧ (C[φn]))
        ∨ (¬P1 ∧ ¬P2 ∧ ... ¬Pn-1 ∧ ¬Pn ∧ (C[⊥]))
    = (P1 ∧ (C[φ1 ∨ (φ2 ∧ P2) ∨ ... ∨ (φn ∧ Pn)]))
        ∨ (¬P1 ∧ P2 ∧ (C[φ2 ∨ ... ∨ (φn ∧ Pn)]))
        ...
        ∨ (¬P1 ∧ ¬P2 ∧ ... ¬Pn-1 ∧ Pn (C[φn]))
        ∨ (¬P1 ∧ ¬P2 ∧ ... ¬Pn-1 ∧ ¬Pn ∧ (C[⊥]))
```
Note that if we have confluence (`Pi ∧ Pj -> φi=φj`) or the predicates
are disjoint (`Pi ∧ Pj=⊥` f∨ `i<>j`, which is just a particular kind of
confluence), then the above becomes
```
C[(φ1 ∧ P1) ∨ (φ2 ∧ P2) ∨ ... ∨ (φn ∧ Pn)]
    = (P1 ∧ (C[φ1 ∨ (φ2 ∧ P1 ∧ P2) ∨ ... ∨ (φn ∧ P1 ∧ Pn)]))
        ∨ (¬P1 ∧ P2 ∧ (C[φ2 ∨ ... ∨ (φn ∧ P2 ∧ Pn)]))
        ...
        ∨ (¬P1 ∧ ¬P2 ∧ ... ¬Pn-1 ∧ Pn ∧ (C[φn]))
        ∨ (¬P1 ∧ ¬P2 ∧ ... ¬Pn-1 ∧ ¬Pn ∧ (C[⊥]))
    = (P1 ∧ C[φ1])
        ∨ (¬P1 ∧ P2 ∧ C[φ2])
        ...
        ∨ (¬P1 ∧ ¬P2 ∧ ... ¬Pn-1 ∧ Pn ∧ C[φn])
        ∨ (¬P1 ∧ ¬P2 ∧ ... ¬Pn-1 ∧ ¬Pn ∧ (C[⊥]))
    = (P1 ∧ C[φ1])
        ∨ (P2 ∧ C[φ2])
        ...
        ∨ (Pn ∧ C[φn])
        ∨ (¬P1 ∧ ¬P2 ∧ ... ¬Pn-1 ∧ ¬Pn ∧ (C[⊥]))
```

Decision
--------

We will move to the new representation, `(term, predicate ∧ substitution)`
for our evaluation cases and split in a bottom-up fashion.

What happens when encountering quantifiers is left open for now.
