Rewrite rules with priorities
=============================

Background
----------

Priorities allow writing case-based `K` code that closer resembles functional
languages, i.e. it allows saying things like "Apply this rule first,
if that doesn't work try this other one, if that also doesn't work try
this, and so on". The `owise` attribute is a special case of this.

### K syntax

The `K` code looks roughly like this:

```
rule t(X) ⇒ s(X) requires P(X) [priority(<number>)]
```

where the highest priority is the one with the lowest number.

As an example, if `A(X)` rewrites to
* `B(X)` if `X<0`
* `C(X)` if `X≥0 ∧ X<1`
* `D(X)` if `X≥1`,
we could write the following rules:

```
rule A(X) ⇒ B(X) requires X <Int 0 [priority(1)]
rule A(X) ⇒ C(X) requires X <Int 1 [priority(2)]
rule A(X) ⇒ D(X)                   [priority(3)]
```

### Non-priority rules in Kore

When transformed into `Kore`, non-priority rewrite rules usually look like

```
φ(X) ⇒ ψ(X)
```

Where `φ(X)` can be written as `t(X) ∧ P(X)` where `t(X)` is a
(function-like) term and `P(X)` is a predicate, corresponding to the
left-hand term and the requires clause in the `K` rule.

Applying a rule to a configuration `C(Y)` is equivalent to unifying
`C(Y)` with `φ(X)` and transforming `ψ(X)` with the result, i.e.
computing `∃ X . ⌈ C(Y) ∧ φ(X) ⌉ ∧ ψ(X)`.

A rule cannot be applied if unification fails, i.e. if
`⌈ C(Y) ∧ φ(X) ⌉` is `⊥`.

Encoding priority rules in Kore
-------------------------------

There are at least two options for encoding these rules: we can encode
the requirement that we couldn't use the higher-priority rules as a predicate,
which would allow us to use the same format for rules (`φ(X) ⇒ ψ(X)`
where `φ(X)` can be written as `t(X) ∧ P(X)` where `t` is a term and
`P(X)` is a predicate) or we could encode that requirement as an expression
that is neither a term, a predicate, or a combination of these.

The `K` frontend currently uses the "expression" option. We will discuss
the two options in detail below.

### Priority expression (non-predicate/term)

Let us notice that, given a rule `φ(X) ⇒ ψ(X)`, we could describe
all configurations to which it applies with `∃ X . phi(X)`. Therefore,
if we have only two rules (`φᵢ` includes the requires predicate):
```
φ₁(X) ⇒ ψ₁(X) [priority(p₁)]
φ₂(X) ⇒ ψ₂(X) [priority(p₂)]
```
and, if we also know that `p₁ < p₂`, we could replace them with
```
φ₁(X) ⇒ ψ₁(X)
(φ₂(X) ∧ ¬ ∃ X₁ . φ₁(X₁)) ⇒ ψ₂(X)
```

Let us see that this is, indeed, the case. We would like to show that the
result of applying the second rule is the same.

The result of applying the second non-priority rule to `C(Y)` is
```
∃ X . ⌈ C(Y) ∧ (φ₂(X) ∧ ¬ ∃ X₁ . φ₁(X₁)) ⌉ ∧ ψ₂(X)
```

Applying the second rule when the first one doesn't work makes most sense for
function-like patterns. For non-function-like patterns understanding what it
means to apply the rules separately is slightly trickier, but it can be
reduced to splitting the pattern into function like ones (if possible) and
applying the rules on the functional components.

If C(Y) is functional, then the first rule does not apply iff
`¬ ∃ X₁ ⌈ C(Y) ∧ φ₁(X₁) ⌉`, so
applying the second rule when the first one does
not work is equivalent to computing
```
∃ X .
    ⌈ C(Y) ∧ φ₂(X) ⌉
    ∧ ¬ ∃ X₁ ⌈ C(Y) ∧ φ₁(X₁) ⌉
    ∧ ψ₂(X)
```

Let's see if the two are equivalent:

```
∃ X .
    ⌈ C(Y) ∧ φ₂(X) ⌉
    ∧ ¬ ∃ X₁ . ⌈ C(Y) ∧ φ₁(X₁) ⌉
    ∧ ψ₂(X)
===
// ⌈⌉ commutes with ∃
∃ X .
    ⌈ C(Y) ∧ φ₂(X) ⌉
    ∧ ¬ ⌈ ∃ X₁ . C(Y) ∧ φ₁(X₁) ⌉
    ∧ ψ₂(X)
===
// ∃ X . A ∧ B(X)  ===  A ∧ ∃ X . B(X)
∃ X .
    ⌈ C(Y) ∧ φ₂(X) ⌉
    ∧ ¬ ⌈ C(Y) ∧ ∃ X₁ . φ₁(X₁) ⌉
    ∧ ψ₂(X)
===
// If P is a predicate, ⌈ A ⌉ ∧ P === ⌈ A ∧ P ⌉
∃ X .
    ⌈
        C(Y) ∧ φ₂(X)
        ∧ ¬ ⌈ C(Y) ∧ ∃ X₁ . φ₁(X₁) ⌉
    ⌉
    ∧ ψ₂(X)
===
// A ∧ ¬ (A ∧ B) = A ∧ ¬ B
∃ X .
    ⌈
        C(Y) ∧ φ₂(X)
        ∧ ¬ (C(Y) ∧ ⌈ C(Y) ∧ ∃ X₁ . φ₁(X₁) ⌉)
    ⌉
    ∧ ψ₂(X)
===
// if A is functional, then A ∧ B = A ∧ ⌈ A ∧ B ⌉
∃ X .
    ⌈
        C(Y) ∧ φ₂(X)
        ∧ ¬ (C(Y) ∧ ∃ X₁ . φ₁(X₁))
    ⌉
    ∧ ψ₂(X)
===
// A ∧ ¬ (A ∧ B) = A ∧ ¬ B
∃ X .
    ⌈ C(Y) ∧ φ₂(X) ∧ ¬ ∃ X₁ . φ₁(X₁) ⌉
    ∧ ψ₂(X)
```

We can generalize this in the following way:

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
    ∧ ¬ (∃ Xₙ . φₙ(Xₙ) ∧ Pₙ(Xₙ))
    ⇒ ψ(X)
```
Strictly speaking, we should have the left hand side of the encoding of the
respective rules under `∃ Xᵢ` above, but the two forms should be
equivalent.

### Priority predicate

If we have only two rules
```
φ₁(X) ⇒ ψ₁(X) requires P₁(X) [priority(p₁)]
φ₂(X) ⇒ ψ₂(X) requires P₂(X) [priority(p₂)]
```
and, if we also know that `p₁ < p₂`, we could replace them with
```
φ₁(X) ⇒ ψ₁(X) requires P₁(X)
φ₂(X) ⇒ ψ₂(X)
    requires P₂(X)
        ∧ ¬ ∃ X₁ . ⌈φ₂(X) ∧ φ₁(X₁)⌉ ∧ P₁(X₁)
```

Applying the second rule with a priority predicate means computing:
```
∃ X . ⌈ C(Y) ∧ φ₂(X) ∧ P₂(X) ∧ ¬ ∃ X₁ . ⌈φ₂(X) ∧ φ₁(X₁)⌉ ∧ P₁(X₁)⌉ ∧ ψ₂(X)
===
// A ∧ ¬ B = A ∧ ¬ (A ∧ B)
∃ X . ⌈ C(Y) ∧ φ₂(X) ∧ P₂(X) ∧ ¬ ∃ X₁ . φ₂(X) ∧ ⌈φ₂(X) ∧ φ₁(X₁)⌉ ∧ P₁(X₁) ⌉ ∧ ψ₂(X)
===
// Assuming φ₂(X) is functional,
// φ₂(X) ∧ ⌈φ₂(X) ∧ φ₁(X₁)⌉ === φ₂(X) ∧ φ₁(X₁)
∃ X . ⌈ C(Y) ∧ φ₂(X) ∧ P₂(X) ∧ ¬ ∃ X₁ . φ₂(X) ∧ φ₁(X₁) ∧ P₁(X₁) ⌉ ∧ ψ₂(X)
===
// ∃ X₁ . A ∧ B(X)  ===  A ∧ ∃ X₁ . B(X)
∃ X . ⌈ C(Y) ∧ φ₂(X) ∧ P₂(X) ∧ ¬ (φ₂(X) ∧ ∃ X₁ . φ₁(X₁) ∧ P₁(X₁)) ⌉ ∧ ψ₂(X)
===
// A ∧ ¬ (A ∧ B) = A ∧ ¬ B
∃ X . ⌈ C(Y) ∧ φ₂(X) ∧ P₂(X) ∧ ¬ ∃ X₁ . φ₁(X₁) ∧ P₁(X₁) ⌉ ∧ ψ₂(X)
===
// A ∧ ¬ (A ∧ B) = A ∧ ¬ B
∃ X . ⌈ C(Y) ∧ φ₂(X) ∧ P₂(X) ∧ ¬ ∃ X₁ . C(Y) ∧ φ₁(X₁) ∧ P₁(X₁) ⌉ ∧ ψ₂(X)
```
which is the same as above (above `P₁` and `P₂` are included in `φ₁` and `φ₂`).

### Discussion

Using the priority expression (the option that's currently implemented)
is cleaner form a theoretical point of view since it requires only that the
configuration is function-like, and, arguably, not even that is needed,
i.e. the priority expression could work as the definition of applying priority
rules. It also matches what the Haskell backend produces for remainder pattern
when rewriting.

The priority predicate requires, additionally, that the left hand side of any
priority rule is function-like. This means that it would prevent people from
using rules containing `#Or`. It is possible that one could overcome this
limitation, though that would require furhter investigations.

It also makes it easier to implement rule merging, since a `LHS ⇒ RHS`
rule would always have a  `LHS` of the form `t ∧ P` where `t` is a term and
`P` is a predicate. This would not make a difference for the Haskell backend
because priority expression/predicate is removed from the `LHS` and is not
evaluated explicitly when rewriting anyway, so, in practice, the `LHS` can
be treated as if it is of the form `t ∧ P`.

I recommend using the priority expression.


