Using configuration predicates
==============================

Background
----------

We are representing rewriting configurations as
`term ∧ predicate ∧ substitution` where the substitution is a special
kind of predicate of the form `var₁ = φ₁ ∧ var₂ = φ₂ ∧ ...`.

We will denote by "predicate" both the "predicate" above and the
predicate-substitution combination. The text below should work with both,
so read it with whatever interpretation is more convenient.

Problems
--------

We would like to use the predicate in a configuration in at least two ways:

1. Applying substitutions in a configuration
1. Pruning evaluation branches faster, somewhere in the middle of simplifying a
configuration, without waiting for the local predicates to reach the top of
the configuration in order to detect contradictions.

How do we do that?

Examples
--------

Let us consider applying the `x=f(y)` substitution to the following terms:
```
σ(x)
∃ x . σ(x)
\exist y . σ(x, y)
¬ (σ(x))
```

The results should be (the "How it works" section explains why):
```
σ(f(y))
∃ x . σ(x)
\exist y' . σ(f(y), y')
¬ σ(f(x))
```

Let us assume that we have two axioms:
`g(x) = 1 if x ≠ 0` and `g(x) = 0 if x = 0`.
Let us try to simplify the following configurations:
```
1. σ(g(x)) ∧ (x ≠ 0)
2. (∃ x . g(x)) ∧ (x ≠ 0)
3. (\exist y . σ(g(x), y)) ∧ (x ≠ 0)
4. (¬ g(x)) ∧ (x ≠ 0)
```

For 1, 3 and 4 we can immediately evaluate `g(x)` to `1`, skipping the `x=0`
case, so the results should be (again, see the "How it works" section for
details):

```
1. σ(1) ∧ (x ≠ 0)
2. (∃ x . (1 and x ≠ 0) ∨ (0 and x=0)) ∧ (x ≠ 0)
3. (∃ y . σ(1, y)) ∧ (x ≠ 0)
4. (¬ 1) ∧ (x ≠ 0)
```

How to use predicates and substitutions.
----------------------------------------

Let `P` be a predicate and let `φ(x)` be a formula in which all occurrences
of `x` are free, and none has a quantifier for a free variable in `P` above it.

Then `φ(ψ)∧ P = φ(ψ ∧ P) ∧ P`

Therefore, above we can, say, rewrite `(¬ g(x)) ∧ (x ≠ 0)` to
`(¬ (g(x) ∧ (x ≠ 0))) ∧ (x ≠ 0)` and we can evaluate
`g(x) ∧ (x ≠ 0)` to `1`.

Similarly, we can apply a substitution inside any kind of term, as long as
quantifiers do not change the meaning of the free variables in the substitution.
Note that in the `\exist y . σ(x, y)` example above we first renamed the
quantified variable to `y'`, and only then we applied the `x=f(y)` substitution.

If we make sure that we never use the same name for a quantified variable and
a free one, and we never re-quantify variables (i.e. we don't have
`∃ x . (... (∃ x . φ) ...)`), then we are free to use the
predicates we have at one level (e.g. the top one) at all lower levels in the
term.


How it works
------------

For simplicity, let us make the above assumption about not re-quantifying
variables.

Since `P` is a predicate, it is either `⊤` or `⊥`.

If `P` is `⊤`, then
```
φ(ψ)∧ P = φ(ψ∧⊤)∧ P = φ(ψ∧ P)∧ P
```

If `P` is `⊥`, then we have:
```
φ(ψ)∧ P = ⊥
φ(ψ∧ P)∧ P = bottom
```
therefore we have
```
φ(ψ)∧ P = φ(ψ∧ P)∧ P
```

This means that, with the assumptions above, we can always "and" with
`P` inside a formula.
