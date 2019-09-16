# Remainders for priority rules

## Problem

Consider all the `n` rules (`1 ≤ i ≤ n`)

```
Lᵢ(X) ⇒ Rᵢ(X)  // Rule strongᵢ
```

Having higher priority than a rule

```
L(X) ⇒ R(X)  // Rule weak
```

Then the priority encoding of `Rule weak` is:

```
¬ (∃ X₁. L₁(X₁)) ∧ ... ∧ ¬ (∃ Xₙ. Lₙ(Xₙ)) ∧ L(X) ⇒ R(X).  // Rule weak (a)
```

Attempting to apply all rules `Rule strongᵢ` to a configuration `ψ₀` yields a
remainder `ψ₀'`

```
¬ (∃ X₁. ⌈ψ₀ ∧ L₁(X₁)⌉) ∧ ... ∧ ¬ (∃ Xₙ. ⌈ψ₀ ∧ Lₙ(Xₙ)⌉) ∧ ψ₀.
```

We would like to show that the result of applying the simplified `Rule weak`
to the remainder `ψ₀'` is equivalent to applying the `Rule weak(a)`
to the original configuration `ψ₀`.


## Assumptions

We will make the standard assumptions about configurations and rewrite rules, i.e.,
`ψ₀`, `L(X)`, and `Lᵢ(Xᵢ)` (for each `i`) are function-like.
 
## Justification

We need to show that:

```
∃ X₂. ⌈¬ (∃ X₁. ⌈ψ₀ ∧ L₁(X₁)⌉) ∧ ... ∧ ¬ (∃ Xₙ. ⌈ψ₀ ∧ Lₙ(Xₙ)⌉) ∧ ψ₀ ∧ L(X)⌉ ∧ R(X)
===
∃ X₂. ⌈ψ₀ ∧ ¬ (∃ X₁. L₁(X₁)) ∧ ... ∧ ¬ (∃ Xₙ. Lₙ(Xₙ)) ∧ L(X)⌉ ∧ R(X)
```

It suffices to show

```
ψ₀ ∧ ¬ (∃ X₁. ⌈ψ₀ ∧ L₁(X₁)⌉) ∧ ... ∧ ¬ (∃ Xₙ. ⌈ψ₀ ∧ Lₙ(Xₙ)⌉)
===
ψ₀ ∧ ¬ (∃ X₁. L₁(X₁)) ∧ ... ∧ ¬ (∃ Xₙ. Lₙ(Xₙ))
```

From [Configuration Splitting Simplification](2018-11-08-Configuration-Splitting-Simplification.md) we know that 

```
ψ₀ ∧ ¬ (∃ Xᵢ. Lᵢ(Xᵢ)) === ψ₀ ∧ ¬ (∃ Xᵢ. ⌈ψ₀ ∧ Lᵢ(Xᵢ)⌉)
```

which we can iterate to prove the identity above.

