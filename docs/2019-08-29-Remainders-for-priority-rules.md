# Remainders for priority rules

## Problem

Consider two rules to be applied in priority order,

```
L₁(X) ⇒ R₁(X)  // Rule 1

¬ (∃ X₁. L₁(X₁)) ∧ L₂(X) ⇒ R₂(X).  // Rule 2(a)
```

Applying `Rule 1` to a configuration `ψ₀` yields the result `ψ₁`,

```
∃ X₁. ⌈ψ₀ ∧ L₁(X₁)⌉ ∧ R₁(X₁)
```

and the remainder `ψ₀'`,

```
¬ (∃ X₁. ⌈ψ₀ ∧ L₁(X₁)⌉) ∧ ψ₀.
```

We would like to show that the result of applying the simplified rule

```
L₂(X) ⇒ R₂(X)  // Rule 2(b)
```

to the remainder `ψ₀'` is equivalent to applying the `Rule 2(a)` to the original configuration `ψ₀`,

```
∃ X₂. ⌈¬(∃ X₁. ⌈ψ₀ ∧ L₁(X₁)⌉) ∧ ψ₀ ∧ L₂(X₂)⌉ ∧ R₂(X₂)
===
∃ X₂. ⌈¬(∃ X₁. L₁(X₁)) ∧ ψ₀ ∧ L₂(X₂)⌉ ∧ R₂(X₂)
```

i.e. that,

```
¬ (∃ X₁. ⌈ψ₀ ∧ L₁(X₁)⌉) ∧ ψ₀
===
¬ (∃ X₁. L₁(X₁)) ∧ ψ₀.
```

## Solution

For brevity, we denote `∃L₁ = ∃ X₁. L₁(X₁)`.

We move the quantifier in the first equation inside `⌈_⌉`,

```
¬ (∃ X₁. ⌈ψ₀ ∧ L₁(X₁)⌉) ∧ ψ₀
===
¬ ⌈ψ₀ ∧ ∃ X₁. L₁(X₁)⌉ ∧ ψ₀
===
¬ ⌈ψ₀ ∧ ∃L₁⌉ ∧ ψ₀.
```

Our objective is to show

```
¬⌈ψ₀ ∧ ∃L₁⌉ ∧ ψ₀ = ¬∃L₁ ∧ ψ₀.
```

We choose to solve the equivalent problem,

```
∀ x. x ∈ (¬⌈ψ₀ ∧ ∃L₁⌉ ∧ ψ₀) = x ∈ (¬∃L₁ ∧ ψ₀).
```

```
∀ x. x ∈ (¬⌈ψ₀ ∧ ∃L₁⌉ ∧ ψ₀) = x ∈ (¬∃L₁ ∧ ψ₀)
===
// x ∈ (A ∧ B) = (x ∈ A) ∧ (x ∈ B)
∀ x. (x ∈ ¬⌈ψ₀ ∧ ∃L₁⌉) ∧ (x ∈ ψ₀) = (x ∈ ¬∃L₁) ∧ (x ∈ ψ₀)
===
// for predicate P, x ∈ P = P
∀ x. ¬⌈ψ₀ ∧ ∃L₁⌉ ∧ (x ∈ ψ₀) = (x ∈ ¬∃L₁) ∧ (x ∈ ψ₀)
===
// for predicate P, (P ∧ φ₁ = P ∧ φ₂) = P ∧ (φ₁ = φ₂) ∨ ¬P
∀ x. (x ∈ ψ₀) ∧ (¬⌈ψ₀ ∧ ∃L₁⌉ = x ∈ ¬∃L₁) ∨ ¬(x ∈ ψ₀)
===
// ¬ ⌈φ₁ ∧ φ₂⌉ = ∀ y. ⌊ ¬(y ∈ φ₁) ∨ ¬(y ∈ φ₂) ⌋
∀ x. (x ∈ ψ₀) ∧ ((∀ y. ⌊ ¬(y ∈ ψ₀) ∨ ¬(y ∈ ∃L₁) ⌋) = x ∈ ¬∃L₁) ∨ ¬(x ∈ ψ₀)
===
// instantiate ∀ y. at x
∀ x. (x ∈ ψ₀) ∧ (⌊ ¬(x ∈ ψ₀) ∨ ¬(x ∈ ∃L₁) ⌋ = x ∈ ¬∃L₁) ∨ ¬(x ∈ ψ₀)
===
// for predicate P, ⌊ P ⌋ = P
∀ x. (x ∈ ψ₀) ∧ ((¬(x ∈ ψ₀) ∨ ¬(x ∈ ∃L₁)) = x ∈ ¬∃L₁) ∨ ¬(x ∈ ψ₀)
===
// for predicate P, P ∧ (φ₁ = φ₂) = P ∧ ( (P ∧ φ₁) = φ₂ )
∀ x. (x ∈ ψ₀) ∧ ((x ∈ ψ₀) ∧ (¬(x ∈ ψ₀) ∨ (x ∈ ψ₀) ∧ ¬(x ∈ ∃L₁)) = x ∈ ¬∃L₁) ∨ ¬(x ∈ ψ₀)
===
// A ∧ ¬A = ⊥
∀ x. (x ∈ ψ₀) ∧ ((x ∈ ψ₀) ∧ ¬(x ∈ ∃L₁)) = x ∈ ¬∃L₁) ∨ ¬(x ∈ ψ₀)
===
// for predicate P, P ∧ (φ₁ = φ₂) = P ∧ ( (P ∧ φ₁) = φ₂ )
∀ x. (x ∈ ψ₀) ∧ (¬(x ∈ ∃L₁) = x ∈ ¬∃L₁) ∨ ¬(x ∈ ψ₀)
===
// ¬(x ∈ φ) = x ∈ ¬φ
∀ x. (x ∈ ψ₀) ∧ (x ∈ ¬∃L₁ = x ∈ ¬∃L₁) ∨ ¬(x ∈ ψ₀)
===
// (A = A) = ⊤
∀ x. (x ∈ ψ₀) ∨ ¬(x ∈ ψ₀)
===
// A ∨ ¬A = ⊤
∀ x. ⊤
===
⊤
```
