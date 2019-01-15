# Attributes

As pointed out in [Attributes as Patterns](../design-decisions/2018-07-25
Attributes as patterns.md), attributes are encoded as Kore patterns that only
use application and string literals.

## Axiom Pattern Attributes

Kore.Step.AxiomPatterns

Attributes specific to interpreting axiom patterns.

### Assoc

Associativity axiom

```
assoc{}()
```

Axioms with this attribute should not be used for evaluating functions.

### Comm

Commutativity axiom

```
comm{}()
```

Axioms with this attribute should not be used for evaluating functions.

### HeatCool

Heating and cooling axiom

```
heat{}()
cool{}()
```

In each execution step, the execution strategy first heats the configuration,
applies the normal rules (without `heat{}()` and `cool{}()`), and cools the
result.


### Idem

Idempotency axiom

```
idem{}()
```

Axioms with this attribute should not be used for evaluating functions.

### ProductionID

```
productionID{}("id")
```

### Trusted

```
trusted{}()
```

Spec axioms with this attribute are excluded from verification.

### Unit

```
unit{}()
```

Axioms with this attribute should not be used for evaluating functions.


## Stepper Attributes

Kore.Step.StepperAttributes

Attributes used during Kore execution.

### Constructor

```
constructor{}()
```

A symbol is injective if it is given the `injective` attribute, the
`constructor` attribute, or the `sortInjection` attribute.

### Function

```
function{}()
```

A symbol is a function if it is given the `function` attribute or if it is
functional.

### Functional

```
functional{}()
```

A symbol is functional if it is given the `functional` attribute or the
`sortInjection` attribute.

### Hook

```
hook{}("BUILTIN.name")
```

The string `"BUILTIN.name"` is used to lookup for known builtins.

### Injective

```
injective{}()
```

A symbol is injective if it is given the `injective` attribute, the
`constructor` attribute, or the `sortInjection` attribute.

### Smtlib

The `smtlib` attribute specifies how a Kore application pattern built with the
symbol can be translated to SMT-LIB 2 list expression for an external SMT
solver.

```
smtlib{}("⟨S-expression⟩")
```

#### ⟨S-expression⟩ is an atom

```
smtlib{}("max")
```

The atom is used as the head of the list and the arguments of the application
are passed as arguments for the list.

#### ⟨S-expression⟩ is a list

```
smtlib{}("(mod (^ #1 #2) #3)")
```

The list may contain special meta-varialbes `#1`, `#2`, ... (not a valid
SMT-LIB syntax) which indicate the position of the arguments of the application
pattern.

### SortInjection

```
sortInjection{}()
```

A symbol is injective if it is given the `injective` attribute, the
`constructor` attribute, or the `sortInjection` attribute.

A symbol is functional if it is given the `functional` attribute or the
`sortInjection` attribute.

## misc.

### Subsort

```
subsort{Sub,Super}()
```

Used to define subsorting relations, (not necessarily) attached to subsort
axiom. For example,

```
axiom{R} \exists{R} (Val:SortKResult{},
   \equals{SortKResult{}, R}
      (Val:SortKResult{},
       inj{SortBool{}, SortKResult{}} (From:SortBool{})))
   [subsort{SortBool{}, SortKResult{}}()]
```
