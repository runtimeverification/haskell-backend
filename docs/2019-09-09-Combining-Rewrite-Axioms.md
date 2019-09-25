Combining rewrite Axioms
========================

In the
[Polkadot Verification](https://github.com/runtimeverification/polkadot-verification/issues/20)
issue, @ehildenb proposed that we should either apply a chain of rules to a
symbolic configuration consisting of a single variable, or we should be able to
combine rules into a single one. This document details the matching logic
reasoning and assumptions behind these.

Summary
-------

If we have this chain of axioms: `α₁(X₁)⇒β₁(X₁)` … `αₙ(Xₙ)⇒βₙ(Xₙ)` in which
all the LHS are *function-like* and *injection-based*, and all the RHS
except `βₙ(Xₙ)` are *function-like*, then their combined transition is

```
(⌈β₁(X₁)∧α₂(X₂)⌉ ∧ ⌈β₂(X₂)∧α₃(X₃)⌉ ∧ … ∧ ⌈βₙ₋₁(Xₙ₋₁)∧αₙ(Xₙ)⌉ ∧ α₁(X₁))→••…•βₙ(Xₙ)
```

TODO: We may need to figure out how to handle maps, sets, and other structures
based on non-injective symbols.

The general transformation
--------------------------

Let us take a configuration `φ(X)` which is functional,
and which can be a single variable.

Let us also take a configuration `α(X)→•β(X)`, with `α(X)` being functional.
Then, similar to
[basic symbolic execution algorithm](2018-11-08-Applying-Axioms.md), we have:

```
1. α(Y) → •β(Y) // the axiom
1. α(Y) ∧ ⌈α(Y) ∧ φ(X)⌉ → (•β(Y)) ∧ ⌈α(Y) ∧ φ(X)⌉
   // from (1) and propositional reasoning
1. α(Y) ∧ ⌈α(Y) ∧ φ(X)⌉ = α(Y) ∧ φ(X)
   // ML paper Prop. 5.24, needs `α` and `φ` to be functional
1. α(Y) ∧ φ(X) → (•β(Y)) ∧ ⌈α(Y) ∧ φ(X)⌉
   // from (2) and (3)
1. φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → (•β(Y)) ∧ ⌈α(Y) ∧ φ(X)⌉
   // from (3) and (4)
1. φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → ∃ Y . ((•β(Y)) ∧ ⌈α(Y) ∧ φ(X)⌉)
   // FOL reasoning
1. ∀ Y . (φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → ∃ Y . ((•β(Y)) ∧ ⌈α(Y) ∧ φ(X)⌉))
   // All unquantified variables are universal
1. ∀ Y . (φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → ∃ Y’ . ((•β(Y’)) ∧ ⌈α(Y’) ∧ φ(X)⌉))
   // Renaming variables to make things clear
1. ∀ Y .
        ( φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉
        → ∃ Y’ . ((•β(Y’)) ∧ ⌈α(Y’) ∧ φ(X)⌉ ∧ ⌈α(Y) ∧ φ(X)⌉)
        )
   // a ∧ b → c is the same as a ∧ b → c ∧ b
```

When doing normal rewriting, we usually expect to get substitutions for the
variables in `Y` and `Y’` when computing `⌈α(Y) ∧ φ(X)⌉`, which usually allows
us to remove these variables. However, when combining rewriting axioms,
we don’t always get such substitutions, so we need to take a different approach.

First, let us note that if `φ₁`, `φ₂` and `φ₃` are *functional*, then
```
⌈φ₁∧φ₂⌉ ∧ ⌈φ₁∧φ₃⌉
= (φ₁ == φ₂) ∧ (φ₁ == φ₃)
= (φ₁ == φ₂) ∧ (φ₂ == φ₃)
= ⌈φ₁∧φ₂⌉ ∧ ⌈φ₂∧φ₃⌉
```

So we have

```
∀ Y .
   ( φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉
   → ∃ Y’ . ((•β(Y’)) ∧ ⌈α(Y’) ∧ φ(X)⌉ ∧ ⌈α(Y) ∧ φ(X)⌉)
   )
iff
∀ Y .
   ( φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉
   → ∃ Y’ . ((•β(Y’)) ∧ ⌈α(Y’) ∧ φ(X)⌉ ∧ ⌈α(Y’) ∧ α(Y)⌉)
   )
```

Now, if, additionally, `α(Y)` is *constructor-based* (or, at least,
injection-based), then
```
⌈α(Y’) ∧ α(Y)⌉ iff Y = Y’
```
Note that this might also hold in some constrained cases when using
non-constructor LHS, e.g. LHS that use maps or sets.
These are not detailed here.

So, assuming that, we have the following transformations:
```
1. ∀ Y .
      ( φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉
      → ∃ Y’ . ((•β(Y’)) ∧ ⌈α(Y’) ∧ φ(X)⌉ ∧ ⌈α(Y’) ∧ α(Y)⌉)
      )
1. ∀ Y . (φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → ∃ Y’ . ((•β(Y’)) ∧ ⌈α(Y’) ∧ φ(X)⌉ ∧ Y’=Y))
   // Apply the formula above
1. ∀ Y . (φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → ∃ Y’ . ((•β(Y)) ∧ ⌈α(Y) ∧ φ(X)⌉ ∧ (Y’=Y)))
   // Apply the substitution
1. ∀ Y . (φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → ((•β(Y)) ∧ ⌈α(Y) ∧ φ(X)⌉ ∧ (∃ Y’ . Y’=Y)))
   // ∃ Y . ζ ∧ φ(Y) = ζ ∧ ∃ Y . φ(Y)
1. ∀ Y . (φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → ((•β(Y)) ∧ ⌈α(Y) ∧ φ(X)⌉))
   // (∃ Y . Y == ζ) = ⊤
1. φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → ((•β(Y)) ∧ ⌈α(Y) ∧ φ(X)⌉)
   // ∀ is not needed at the top level
1. φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → •β(Y)
   // (a ∧ c) → (b ∧ c) iff (a ∧ c) → b
```

Implementation concerns
-----------------------

### Eliminating variables

Note that if `⌈α(Y) ∧ φ(X)⌉` contains a substitution `y=ζ` then we can apply it
and remove the variable `y` from the expression above (proof not shown here, one
needs to transform
```
∀ Y . (φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → ∃ Y’ . (•β(Y’) ∧ ⌈α(Y’) ∧ φ(X)⌉))).
```
into
```
(∃ Y . (φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉)) → ∃ Y’ . (•β(Y’) ∧ ⌈α(Y’) ∧ φ(X)⌉)
   // ∀ x . (φ(x) -> ζ)  ==  (∃ x . φ(x)) -> ζ
```
above to make it work).

### Using function-like patterns

Usually `φ(X)` and `α(X)` are only function-like, but the above requires
functional patterns. We will show that the same formula also works for function-like patterns.

```
1. φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → •β(Y)
   // Works only for functional patterns
1. (⌈φ(X)⌉ ∧ ⌈α(Y)⌉) → (φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → •β(Y))
   // Adding definedness conditions, works for function-like patterns
1. ⌈φ(X)⌉ ∧ ⌈α(Y)⌉ ∧ φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → •β(Y)
   // a → (b → c) = (a ∧ b) → c
1. φ(X) ∧ ⌈α(Y) ∧ φ(X)⌉ → •β(Y)
   // If a → b then a ∧ b = a
   // ⌈a ∧ b⌉ → ⌈a⌉
   // ⌈α(Y) ∧ φ(X)⌉ -> ⌈α(Y)⌉
   // ⌈α(Y) ∧ φ(X)⌉ -> ⌈φ(X)⌉
```

### Combining rewrite rules

Let’s say that our axioms are `α₁(X₁)⇒β₁(X₁)` … `αₙ(Xₙ)⇒βₙ(Xₙ)`.

Let us attempt to combine `α₁(X₁)⇒β₁(X₁)` with `α₂(X₂)⇒β₂(X₂)`. Let us assume
that, when applying `α₂(X₂)⇒β₂(X₂)` to `β₁(X₁)` as described above, we get
```
β₁(X₁) ∧ ⌈β₁(X₁)∧α₂(X₂)⌉ → •β₂(X₂)
```

We have an axiom `a -> •b` and we inferred `(P ∧ b) → •c`. Then, from the
axiom, we can infer `(P ∧ a) -> •(P ∧ b)`. By combining the two inferences we
get `(P ∧ a) → ••(P ∧ c)`, which is equivalent to `(P ∧ a) → ••c`.

The above holds because of this:
```
Hypothesis: a → •b and b → •c
From b → •c, by framing: •b → ••c
From a → •b and •b → ••c: a → ••c
```

Then we have
```
(⌈β₁(X₁)∧α₂(X₂)⌉ ∧ α₁(X₁))→••β₂(X₂)
```

By applying this iteratively, we get

```
(⌈β₁(X₁)∧α₂(X₂)⌉ ∧ ⌈β₂(X₂)∧α₃(X₃)⌉ ∧ ... ⌈βₙ₋₁(Xₙ₋₁)∧αₙ(Xₙ)⌉ ∧ α₁(X₁))→••…•βₙ(Xₙ)
```

### Removing Substitutions

Let us take an example. Let us say that we have two axioms:

```
(X + Y) ~> R => (X +Int Y) ~> R    if isConcrete(X) and isConcrete(Y)
Z ~> ([] * T) ~> S => (Z * T) ~> S   if isConcrete(Z)
```

If we try to combine them, we would get

```
(X + Y) ~> R => (Z * T) ~> S
    if  isConcrete(X) and isConcrete(Y) and isConcrete(Z)
        and (Z == X +Int Y) and (R == ([] * T ~> S))
```

Now, this is a bit ugly, but we can apply the substitutions for `Z` and `R`,
getting

```
(X + Y) ~> [] * T ~> S => ((X +Int Y) * T) ~> S
    if  isConcrete(X) and isConcrete(Y) and isConcrete(X +Int Y)
        and (Z == X +Int Y) and (R == ([] * T ~> S))

// isConcrete(X +Int Y) is true
(X + Y) ~> [] * T ~> S => ((X +Int Y) * T) ~> S
    if  isConcrete(X) and isConcrete(Y)
        and (Z == X +Int Y) and (R == ([] * T ~> S))
```

This is better, but, since we're not actually using `Z` and `R`, we can
remove the substitution:

```
(X + Y) ~> [] * T ~> S => ((X +Int Y) * T) ~> S
    if  isConcrete(X) and isConcrete(Y)
```

To make it more formal, let us say that our axioms are
`α₁(X₁)⇒β₁(X₁)` … `αₙ(Xₙ)⇒βₙ(Xₙ)` and
`P(X₁, …, Xₙ)` is the merge predicate, and that the merged rule is
`α₁(X₁) ∧ P(X₁, …, Xₙ) ⇒ βₙ(Xₙ)`.

Let us further assume that there is some predicate `Q(X₁, …, Xₙ)` and
a substitution `S(Y)` such that `P(X₁, …, Xₙ) = Q(X₁, …, Xₙ) ∧ S(Y)` and
the substituted variables do not occur on the right hand side of any
substitution.

Then we can apply the substitution to `α₁`, `βₙ` and `Q`, getting `α'`, `β'` and
`Q'` such that the variables in `Y` do not occur free in them.

Then the rule becomes
```
α₁(X₁) ∧ Q(X₁, …, Xₙ) ∧ S(Y) ⇒ βₙ(Xₙ)
α₁(X₁) ∧ Q(X₁, …, Xₙ) ∧ S(Y) ⇒ βₙ(Xₙ) ∧ S(Y)  // a ∧ c → b iff a ∧ c → b ∧ c
α' ∧ Q' ∧ S(Y) ⇒ β' ∧ S(Y)  // applying the substitution
α' ∧ Q' ∧ S(Y) ⇒ β'  // a ∧ c → b iff a ∧ c → b ∧ c
∀ Y . α' ∧ Q' ∧ S(Y) ⇒ β'  // Explicit quantification
α' ∧ Q' ∧ (∃ Y . S(Y)) ⇒ β'  // ∀ x . (φ(x) -> ζ)  ==  (∃ x . φ(x)) -> ζ
α' ∧ Q' ⇒ β'  // (∃ x . x=φ) is always top
```

### Distributing over predicate disjunction

This is useful when we're doing AC unification, say, because two merged rules
use a map, perhaps the `state` map.

If the merge rule is `α₁(X₁) ∧ (P(X₁, …, Xₙ) ∨ Q(X₁, …, Xₙ)) ⇒ βₙ(Xₙ)` then we
may have substitutions inside `P` and `Q`, but we may not be able to apply them
directly to get a simplified rule. But we can do this:

``
α₁(X₁) ∧ (P(X₁, …, Xₙ) ∨ Q(X₁, …, Xₙ)) ⇒ βₙ(Xₙ)
(α₁(X₁) ∧ P(X₁, …, Xₙ)) ∨ (α₁(X₁) ∧ Q(X₁, …, Xₙ)) ⇒ βₙ(Xₙ)
(α₁(X₁) ∧ P(X₁, …, Xₙ) ⇒ βₙ(Xₙ)) ∧ (α₁(X₁) ∧ Q(X₁, …, Xₙ) ⇒ βₙ(Xₙ))
    // (a ∨ b) -> c iff (a -> c) ∧ (b -> c)
```

so we can get two rules with an `and` between them, which means that we
actually get two separate rules.

Applying rules to some initial configuration
--------------------------------------------

The result is the same as above, except that, if the initial configuration is
`φ(X)`, we get

```
   ( ⌈φ(X)∧α₂(X₁)⌉
   ∧ ⌈β₁(X₁)∧α₂(X₂)⌉
   ∧ ⌈β₂(X₂)∧α₃(X₃)⌉
   ∧ ...
   ∧ ⌈βₙ₋₁(Xₙ₋₁)∧αₙ(Xₙ)⌉
   ∧ φ(X)
   )
→  ••…•βₙ(Xₙ)
```

Now, if `φ(X)=X`, then this formula becomes equivalent to the one above.
