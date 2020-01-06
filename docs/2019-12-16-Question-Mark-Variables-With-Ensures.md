# Meaning of `?` variables in K

## Summary

The frontend syntax uses question mark variables of the form `?X` to refer to
existential variables, and uses `ensures` to specify logical constraints on
those variables.
These variables are only allowed to appear in the RHS of a rule.

When K rules are translated to Kore axioms, the `?` variables are existentially
quantified at the top of the RHS and the `ensures` clause is and-ed to the RHS.

This design document presents four typical language constructs or mathematical
functions that have unspecified or nondeterministic behaviors and shows their
axiomatization in Kore.

We also propose the corresponding K frontend syntax to define some of these
behaviors.

### Implementation concerns

Except for the `fresh` variants (Example B), none of the other are currently
supported by either the K frontend of the Haskell backend.


## Example A: Random Number Construct `rand()`

The random number construct `rand()` is a language construct which could be
easily conceived to be part of the syntax of a programming language:

```
Exp ::= "rand" "(" ")"
```

### Axioms

The intended semantics of `rand()` is that it can rewrite to any integer in
a single step.
Here is its axiom

```
(RAND) \forall I:Int . rand() -> * I
// equivalent form(s)
//     rand() -> \forall I:Int . * I
//     rand() -> * I
// non-equivalent form(s)
//     rand() -> * (\forall I:Int . I)
```

Note that the `(RAND)` axiom is logically equivalent to the following infinitely
many axioms.

```
(RAND0)  rand() -> * 0
(RAND1)  rand() -> * 1
(RAND2)  rand() -> * 2
  ...    ...
(RAND-1) rand() -> * (-1)
(RAND-2) rand() -> * (-2)
  ...    ...
```

One can define variants of `rand()` by further constraining the output variable
as a precondition to the rule.
For example, `randPrime()`, defined below, can rewrite to any _prime number_.

```
(RANDPRIME) \forall P:Int . isPrime(P) -> (randPrime() -> * P)
// equivalent form(s)
//          \forall P:Int . (randPrime() /\ isPrime(P)) -> *P
//          \forall P:Int . randPrime() -> (isPrime(P) -> * P)
//          randPrime() -> \forall P:Int . (isPrime(P) -> * P)
//          remove \forall P:Int in all above three
```

where `isPrime(_)` is a predicate that can be defined in the usual way.

As another example, `randDifferentFromList(Is)` takes a list `Is` of integers
and can rewrite in one step to any integer that is not in `Is`.
Here is its axiom

```
(RANDLIST) \forall Is:List{Int} . \forall I:Int . \neg(I \in Is) -> randDifferentFromList(Is) -> * I
```

### Frontend Syntax

Since all variables are universally quantified, `rand()` and its variants could
be written in the K frontend using regular rules and variables:

```
syntax Exp ::= rand ()
rule rand() => X:Int

syntax Exp ::= randPrime ()
rule randPrime() => X:Int
  requires isPrime(X)

syntax Exp ::= randList (List{Int})
rule randList(Is) => I:Int
  requires notBool (I inList{Int} Is)
```

Note 1: all above are not function symbols, but languages constructs.

Note 2: Currently the frontend does not allow rules with universally quantified
variables in the RHS which are not bound in the LHS.

## Example B: Fresh Integer Construct `fresh(Is)`

The fresh integer construct `fresh(Is)` is a language construct and part of the
PL syntax.

```
Exp ::= ... | "fresh" "(" List{Int} ")"
```

### Axioms

The intended semantics of `fresh(Is)` is that it can always rewrite to an integer
that in not in `Is`.

Note that `fresh(Is)` and `randDifferentFromList(Is)` are different; the former
does not _need_ to be able to rewrite to every integers not in `Is`,
while the latter requires so.

For example, it is _correct_ to implement `fresh(Is)` so it always returns the
smallest positive integer that is not in `Is`, but same implementation for
`randDifferentFromList(Is)` is considered _incorrect_.
In other words, there exist multiple correct implementations of `fresh(Is)`,
some of which may be deterministic, but there only exists a unique
implementation of `randDifferentFromList(Is)`.
Finally, note that `randDifferentFromList(Is)` is a _correct_ implementation
for `fresh(Is)`.

Here is the axiom of `fresh(Is)`

```
(FRESH) \forall Is:List{Int} . \exists I:Int . \neg( I \in Is) /\ (fresh(Is) -> * I)
// equivalent form(s)
//      \forall Is:List{Int} . fresh(Is) -> \exists I:Int . \neg( I \in Is) /\ * I
//      \forall Is:List{Int} . fresh(Is) -> \exists I:Int . * (\neg( I \in Is) /\ I)
//      \forall Is:List{Int} . fresh(Is) -> * \exists I:Int . \neg( I \in Is) /\ I
```

### Frontend Syntax

We use the following K syntax to define `fresh(Is)`

```
syntax Exp ::= fresh (List{Int})
rule fresh(Is:List{Int}) => ?I:Int
  ensures notBool (?I inList{Int} Is)
```

## Example C: Arbitrary Number (Unspecific Function) `arb()`

The function `arb()` is not a PL construct, but a mathematical function.
Therefore, its axioms do not use rewrites but equalities.

### Axioms

The intended semantics of `arb()` is that it is an unspecified nullary function.
The exact return value of `arb()` is unspecified in the semantics but up to the
implementations.
However, being a mathematical function, `arb()` must return the same value in
any one implementation.

The axiom of `arb()` is

```
(ARB) \exists I:Int . arb() = I
//    this is exactly the (Function) axiom
//    this is not equivalent to
//      arb() = (\exists I:Int . I)
```

There are many variants of `arb()`. For example, `arbDifferentFromList(Is)` is
a unspecified function whose return value must be different than those in `Is`.
Here is its axiom

```
(ARBDIFF) \forall Is:List{Is} . \exists I:Int . \neg(I \in Is) /\ arbDifferentFromList(Is) = I
```

Note that `arbDifferentFromList(Is)` is different from `fresh(Is)`, because
`fresh(Is)` _transitions_ to an integer not in `Is` (could be a different one
each time it is used), while `arbDifferentFromList(Is)` _is equal to_ a (fixed)
integer not in `Is`.

### Skolemization

One possible approach to implementing the above would be through
[Skolemization](https://en.wikipedia.org/wiki/Skolem_normal_form),
i.e., by replacing the existential variables with fresh uninterpreted functions
applied to the universally quantified variables.

For example, the `(ARBDIFF)` rule above could be Skolemized to

```
(ARBDIFF') \forall Is:List{Is} . \neg(arbDiffI(Is) \in Is) /\ arbDifferentFromList(Is) = arbDiffI(Is)
```
where
```
arbDiffI : List{Int} -> Int
```

is a symbol satisfying the `(Function)` axiom, without further constraints.

### Frontend Syntax

We do not need special frontend syntax to define `arb()`.
We only need to define it in the usual way as a function
(instead of a language construct), and provide no axioms for it
(the `(Function)` axiom is generated automatically from the `function`
attribute annotation.

The frontend doesn't currently provide a syntax to define the variants of
`arb()`, such as `arbDifferentFromList(Is)` in the above.

We envision two possible solutions:

1. they are not allowed, since the users could themselves Skolemize the axiom

    ```
    syntax Int ::= arbDiffI(List{Int}) [function, functional]
    syntax Int ::= arbDifferentFromList(List{Int}) [function, functional]
    rule arbDifferentFromList(Is:List{Int}) => arbDiffI(Is)
      ensures notBool (arbDiffI(Is) inList{Int} Is)
    ```

   However, this construction seems artificial and it might be better to have
   it being automatically generated from the proposed syntax below.

2. They are allowed, assuming that a `function` annotation in the syntax
   definition, together with the use of `?` variables in the `rhs` of the rule and
   the `ensures` clause would trigger Skolemization and the generation of
   the rule above.
   That is, `adbDifferentFromList` could be written in K as

    ```
    syntax Int ::= arbDifferentFormList(List{Int}) [function]
    rule arbDifferentFromList(Is:List{Int}) => ?I:Int
      ensures notBool (?I inList{Int} Is)
    ```

## Example D: Interval (Non-function Symbols) `interval()`

The symbol `interval(M,N)` is not a PL construct, nor a function in the
first-order sense, but a proper matching-logic symbol, whose interpretation is
in the powerset of its domain.
Its axioms will not use rewrites but equalities.

### Axioms

The intended semantics of `interval(M,N)` is that it equals the _set_ of
integers that are larger than or equal to `M` and smaller than or equal to `N`.
Its axiom is

```
(INTERVAL) \forall M:Int . \forall N:Int . interval(M,N) = \exists X:Int . X:Int /\ X >= M /\ X <= N
```

### Frontend Syntax

The symbol declaration would require a special attribute to signal the fact that
it represents a proper ML symbol which is defined equationally. The precise
name would have to be established, but let's call it here `power-function`
to signal that it's a function interpreted in the powerset of the domain.

```
syntax Int ::= interval(Int, Int) [power-function]
rule interval(M:Int,N:Int) = ?X
    ensures ?X >=Int M andBool ?X <=Int N
```

