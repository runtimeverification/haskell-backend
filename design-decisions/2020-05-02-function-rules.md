# Interpretation of function rules

## Purpose

The purpose of this document is to describe in detail how K function rules will be interpreted in Kore.
We will also summarize the motivation for this decision, that is:
what problems this decision solves.

## Notation

`Xᵢ` and `Yᵢ` refer to element variables.
`{X}` and `{Y}` refer to all variables in the respective family of element variables.
`fun(...)` is a function symbol.
`φ` are arbitrary patterns appearing as the arguments of a function rule.
`ψ` are arbitrary patterns appearing on the right-hand side of function rules.
`Pre` and `Post` are respectively pre- and post-condition patterns.

## Background

The family of K rules defining `fun`,

```.k
rule fun(φ₁ᵢ({Y}), φ₂ᵢ({Y}), ...) => ψᵢ({Y}) requires Preᵢ({Y}) ensures Postᵢ({Y})
```

is interpreted in Kore as

```.kore
axiom \implies(Preᵢ({Y}), (fun(φ₁ᵢ({Y}), φ₂ᵢ({Y}), ...) = ψᵢ({Y})) ∧ Postᵢ({Y})).
```

## Problems

### Partial heads

See also: [kframework/kore#1146](https://github.com/kframework/kore/issues/1146)

Rules with partial heads are potentially unsound.
Consider the family of rules

```.k
rule sizeMap(_ |-> _ M:Map) = 1 +Int sizeMap(M)
rule sizeMap(_ |-> _) = 1
rule sizeMap(.Map) = 0
```

producing axioms

```.kore
axiom sizeMap(concatMap(elementMap(_1, _2), M:Map)) = +Int(1, sizeMap(M))
axiom sizeMap(elementMap(_, _)) = 1
axiom sizeMap(.Map) = 0.
```

Note that the first rule has a partial head;
we can instantiate it at `M = elementMap(_1, _2)` to prove

```.kore
sizeMap(concatMap(elementMap(_1, _2), elementMap(_1, _2))) = +Int(1, sizeMap(M))
sizeMap(\bottom) = +Int(1, sizeMap(elementMap(_1, _2)))
sizeMap(\bottom) = +Int(1, 1)
\bottom = 2.
```

### Or patterns

See also: [kframework/kore#1245](https://github.com/kframework/kore/issues/1245)

The user may write an or-pattern rule such as

```.k
rule fun(A #Or B) => C
```

as shorthand for two rules,

```.k
rule fun(A) = C
rule fun(B) = C
```

Under the current interpretation, this produces an axiom

```.kore
axiom fun(A ∨ B) = C.
```

This axiom does not imply `fun(A) = C` or `fun(B) = C`,
and therefore cannot be used to evaluate `fun`.

### Priority

The `priority` attribute is not properly supported.
The `owise` attribute is supported, but its implementation is inefficient:
work is duplicated by re-checking that the other rules in the family do not apply.

## Solution

The family of K rules defining `fun`,

```.k
rule fun(φ₁ᵢ({Y}), φ₂ᵢ({Y}), ...) => ψᵢ({Y}) requires Preᵢ({Y}) ensures Postᵢ({Y})
```

will be interpreted in Kore as

```.kore
axiom \implies(Preᵢ({Y}) ∧ Argsᵢ({X}, {Y}) ∧ Prioᵢ({X}), (fun(X₁, X₂, ...) = ψᵢ({Y})) ∧ Postᵢ({Y}))
```

where

```.kore
Argsᵢ({X}, {Y}) = (X₁ ∈ φ₁ᵢ({Y})) ∧ (X₂ ∈ φ₂ᵢ({Y})) ∧ ...
Prioᵢ({X}) = ∧ⱼ ¬ ∃ {Y}. Preⱼ({Y}) ∧ Argsⱼ({X}, {Y})
    for all j that priority(rule j) < priority(rule i).
```

The interpretation of simplification rules will not change.

### Partial heads

The troublesome example,

```.k
rule sizeMap(_ |-> _ M:Map) = 1 +Int sizeMap(M)
```

is interpreted in Kore as

```.kore
axiom \implies(X ∈ concatMap(elementMap(_1, _2), M:Map), sizeMap(X) = +Int(1, sizeMap(M))).
```

If `concatMap(_, _)` is undefined,
then the pre-condition `X ∈ concatMap(_, _)` is not satisfied;
therefore, the rule is sound.

### Or patterns

The example or-pattern rule,

```.k
rule fun(A #Or B) => C
```

will be interpreted as

```.kore
axiom \implies(X ∈ (A ∨ B), fun(X) = C).
```

The disjunction distributes over `_ ∈ _`

```.kore
X ∈ (A ∨ B)
= (X ∈ A) ∨ (X ∈ B)
```

and over `\implies`

```.kore
\implies(X ∈ (A ∨ B), fun(X) = C)
= \implies(X ∈ A, fun(X) = C) ∧ \implies(X ∈ B, fun(X) = C)
```

so that the original axiom is equivalent to two axioms, as intended:

```.kore
axiom \implies(X ∈ A, fun(X) = C)
axiom \implies(X ∈ B, fun(X) = C).
```

### Priority

Support for the `priority` attribute is built into this interpretation.
