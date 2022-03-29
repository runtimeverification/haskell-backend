# Interpretation of function rules

Applying function rules in the form of equations is implemented in [`Kore.Equation.Application`](https://github.com/runtimeverification/haskell-backend/blob/master/kore/src/Kore/Equation/Application.hs).

## Purpose

This document

1. describes how function rules are currently interpreted in Kore,
1. exposes some problems with the current approach, and
1. explains how function rules will be interpreted in Kore in the future to solve these problems.

## Notation

`Xᵢ` and `Yᵢ` refer to element variables.
`{X}` and `{Y}` refer to all variables in the respective family of element variables.
`fun(...)` is a function symbol.
`φ` are arbitrary patterns appearing as the arguments of a function rule.
`ψ` are arbitrary patterns appearing on the right-hand side of function rules.
`Pre` and `Post` are respectively pre- and post-condition patterns.

## Background

This section will briefly describe how function rules are interpreted in Kore,
before we continue in the next section to expose some problems with this interpretation.
Consider a K function `fun` described by a family of rules,

```.k
rule fun(φ₁ᵢ({Y}), φ₂ᵢ({Y}), ...) => ψᵢ({Y}) requires Preᵢ({Y}) ensures Postᵢ({Y})
```

Each rule is interpreted in Kore as an axiom,

```.kore
axiom \implies(Preᵢ({Y}), (fun(φ₁ᵢ({Y}), φ₂ᵢ({Y}), ...) = (ψᵢ({Y}) ∧ Postᵢ({Y})))).
```

## Problems

### Partial heads

See also: [runtimeverification/haskell-backend#1146](https://github.com/runtimeverification/haskell-backend/issues/1146)

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
sizeMap(concatMap(elementMap(_1, _2), elementMap(_1, _2))) = +Int(1, sizeMap(elementMap(_1, _2)))
sizeMap(\bottom) = +Int(1, sizeMap(elementMap(_1, _2)))
sizeMap(\bottom) = +Int(1, 1)
\bottom = 2.
```

### Or patterns

See also: [runtimeverification/haskell-backend#1245](https://github.com/runtimeverification/haskell-backend/issues/1245)

Consider this family of rules defining function `fun`,

```.k
rule fun(A) => C
rule fun(B) => C
```

which is interpreted in Kore as two axioms,

```.kore
axiom \implies(\top, (fun(A) = (C ∧ \top)))
axiom \implies(\top, (fun(B) = (C ∧ \top))).
```

The K language offers a shorthand notation,

```.k
rule fun(A #Or B) => C
```

which is intended to be equivalent to the pair of rules above.
Under the current interpretation, this rule produces an axiom,

```.kore
axiom \implies(\top, (fun(A ∨ B) = (C ∧ \top)))
```

which is **not** equivalent to the first interpretation.
Specifically, the first interpretation is satisfied if and only if
`fun(A) = C ∧ fun(B) = C`,
but the second interpretation can be satisfied if
`fun(A) = C ∧ fun(B) = \bottom`
or if
`fun(A) = \bottom ∧ fun(B) = C`.
Therefore, the current interpretation of function rules is not faithful to the user's intent.

### Priority

The `priority` attribute is not properly supported.
The `owise` attribute is supported, but its implementation is inefficient:
work is duplicated by re-checking that the other rules in the family do not apply.

## Solution

The interpretation of simplification rules will not change,
but the family of K rules defining `fun`,

```.k
rule fun(φ₁ᵢ({Y}), φ₂ᵢ({Y}), ...) => ψᵢ({Y}) requires Preᵢ({Y}) ensures Postᵢ({Y})
```

will be interpreted in Kore as

```.kore
axiom \implies(Preᵢ({Y}) ∧ Argsᵢ({X}, {Y}) ∧ Prioᵢ({X}), (fun(X₁, X₂, ...) = (ψᵢ({Y}) ∧ Postᵢ({Y}))))
```

where

```.kore
Argsᵢ({X}, {Y}) = (X₁ ∈ φ₁ᵢ({Y})) ∧ (X₂ ∈ φ₂ᵢ({Y})) ∧ ...
Prioᵢ({X}) = ∧ⱼ ¬ ∃ {Y}. Preⱼ({Y}) ∧ Argsⱼ({X}, {Y})
    for all j that priority(rule j) < priority(rule i).
```

The predicate `Argsᵢ` interprets the argument patterns `φ₁ᵢ` element-wise,
matching the user's intent and (as we will see below) avoiding the problems described above.
The predicate `Prioᵢ` encodes the `priority` attribute in the pre-condition of the rule,
which is now possible only because we have moved argument matching into the `Argsᵢ` pre-condition.

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

The `priority` and `owise` attributes are now encoded explicitly in the
pre-condition of the axiom.
Consider a function,

```.k
rule L:Int <= X:Int < _     => false requires notBool L <=Int X
rule _     <= X:Int < U:Int => false requires notBool X  <Int U [priority(51)]
rule _     <= _     < _     => true                             [owise]
```

which will be interpreted in Kore as axioms

```.kore
axiom
    \implies(
        \and(
            true = notBool(<=Int(L, X)),
            (X₁ ∈ L) ∧ (X₂ ∈ X)
        ),
        _<=_<_(X₁, X₂, X₃) = \and (
            false,
            \top
        )
    )
axiom
    \implies(
        \and(
            true = notBool(<Int(X, U)),
            (X₂ ∈ X) ∧ (X₃ ∈ U),
            \not \exists L X.
                \and(
                    true = notBool(<=Int(L, X)),
                    (X₁ ∈ L) ∧ (X₂ ∈ X)
                )
        ),
        _<=_<_(X₁, X₂, X₃) = \and(
            false,
            \top
        )
    )
axiom
    \implies(
        \and(
            \top,
            \top,
            \and(
                \not \exists L X.
                    \and(
                        true = notBool(<=Int(L, X)),
                        (X₁ ∈ L) ∧ (X₂ ∈ X)
                    ),
                \not \exists X U.
                    \and(
                        true = notBool(<Int(X, U)),
                        (X₂ ∈ X) ∧ (X₃ ∈ U)
                    )
            )
        ),
        _<=_<_(X₁, X₂, X₃) = \and(
            true,
            \top
        )
    )
```
