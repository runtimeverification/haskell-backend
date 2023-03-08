# Meaning of `?` variables in K

## Summary

The frontend syntax uses question mark variables of the form `?X` to refer to
existential variables, and uses `ensures` to specify logical constraints on
those variables.
These variables are only allowed to appear in the RHS of a rule.

When K rules are translated to Kore axioms,  the `ensures` clause is and-ed to
the RHS.
If the rules represent rewrite (semantic) steps or verification claims,
then the `?` variables are existentially quantified at the top of the RHS;
otherwise, if they represent equations, the `?` variables are quantified at the
top of the entire rule.

Note that when both `?`-variables and regular variables are present,
regular variables are (implictly) universally quantified on top of the rule
(already containing the existential quantifications).
This essentially makes all `?` variables depend on all regular variables.

This design document presents four typical language constructs or mathematical
functions that have unspecified or nondeterministic behaviors and shows their
axiomatization in Kore.

We also propose the corresponding K frontend syntax to define some of these
behaviors.

### K-Frontend Syntax Proposal

Currently, the K frontend uses the keyword `rule` to mean both rewrite
(semantic) step axioms and equations for functions.
As we have seen above, these two cases are treated differently, but to
distinguish them, one needs to go back to where the PL constructs or functions
are declared, often in a syntax module that is far away from the rules.
In addition, it can be confusing when the same rule keyword yields completely
different encodings when translated to backend.
Therefore, we propose to
1. throw a deprecation warning for using `rule` to declare equations; and
2. define a new front-end syntax `eq LHS == RHS` for defining equations.

This is also an effort towards the goal of writing explicitly KORE
patterns in the frontend.

### Implementation concerns

Except for the `fresh` variants (Example B), none of the other are currently
supported by either the K frontend or the Haskell backend.

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

#### Rand-like examples

1. `randBounded(M,N)` can rewrite to any integer between `M` and `N`
    ```
    \forall M:Int.\forall N:Int.\forall I:Int.
        I >= M /\ I <= N -> randBounded(M, N) -> * I
    ```

1. `randInList(Is)` takes a list `Is` of items
   and can rewrite in one step to any item in `Is`.

    ```
    \forall Is:List . \forall I . inList(I, Is) -> randInList(Is) -> * I
    ```

1. `randNotInList(Is)` takes a list `Is` of items
   and can rewrite in one step to any item _not_ in `Is`.

    ```
    \forall Is:List . \forall I . \not(I \in Is) -> randNotInList(Is) -> * I
    ```

1. `randPrime()`, can rewrite to any _prime number_.

    ```
    \forall P:Int . isPrime(P) -> randPrime() -> * P
    ```

   where `isPrime(_)` is a predicate that can be defined in the usual way.

### Frontend Syntax

Since all variables are universally quantified, `rand()` and its variants could
be written in the K frontend using regular rules and variables:

```
syntax Exp ::= rand ()
rule rand() => X:Int

syntax Exp ::= randBounded(Int, Int)
rule randBounded(M, N) => I
  requires M <=Int I andBool I <=Int N

syntax Exp ::= randInList (List)
rule randInList(Is) => I
  requires I inList Is

syntax Exp ::= randNotInList (List)
rule randNotInList(Is) => I
  requires notBool(I inList Is)

syntax Exp ::= randPrime ()
rule randPrime() => X:Int
  requires isPrime(X)
```

Note 1: all above are not function symbols, but language constructs.

Note 2: Currently the frontend does not allow rules with universally quantified
variables in the RHS which are not bound in the LHS.

Note 3. Allowing these rules in a concrete execution engine would require an
algorithm for generating concrete instances for such variables, satisfying the
given constraints.
Hence, it might be useful to mark these rules with a specific keyword to signal
this fact.

## Example B: Fresh Integer Construct `fresh(Is)`

The fresh integer construct `fresh(Is)` is a language construct and part of the
PL syntax.

```
Exp ::= ... | "fresh" "(" List{Int} ")"
```

### Axioms

The intended semantics of `fresh(Is)` is that it can always rewrite to an integer
that in not in `Is`.

Note that `fresh(Is)` and `randNotInList(Is)` are different; the former
does not _need_ to be able to rewrite to every integers not in `Is`,
while the latter requires so.

For example, it is _correct_ to implement `fresh(Is)` so it always returns the
smallest positive integer that is not in `Is`, but same implementation for
`randNotInList(Is)` might be considered _inadequate_.
In other words, there exist multiple correct implementations of `fresh(Is)`,
some of which may be deterministic, but there only exists a unique
implementation of `randNotInList(Is)`.
Finally, note that `randNotInList(Is)` is a _correct_ implementation
for `fresh(Is)`.

Here is the axiom of `fresh(Is)`

```
(FRESH) \forall Is:List{Int} . \exists I:Int .
    \neg( I \in Is) /\ (fresh(Is) -> * I)

// equivalent form(s)
//  \forall Is:List{Int} . fresh(Is) -> \exists I:Int . \neg( I \in Is) /\ * I
//  \forall Is:List{Int} . fresh(Is) -> \exists I:Int . * (\neg( I \in Is) /\ I)
//  \forall Is:List{Int} . fresh(Is) -> * \exists I:Int . \neg( I \in Is) /\ I
```

### Frontend Syntax

We use the following K syntax to define `fresh(Is)`

```
syntax Exp ::= fresh (List{Int})
rule fresh(Is:List{Int}) => ?I:Int
  ensures notBool (?I inList{Int} Is)
```

A variant of this would be a `choiceInList(Is)` language construct which would
choose some number from a list:

```
syntax Exp ::= choiceInList (List{Int})
rule choiceInList(Is:List{Int}) => ?I:Int
  ensures ?I inList{Int} Is
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

There are many variants of `arb()`. For example, `arbInList(Is)` is
an unspecified function whose return value must be an element from `Is`.
Here is its axiom

```
(ARB) \forall Is:List{Is} . \exists I:Int . I \in Is /\ arbNotInList(Is) = I
```

Note that `arbInList(Is)` is different from `choiceInList(Is)`, because
`choiceInList(Is)` _transitions_ to an integer in `Is` (could be a different one
each time it is used), while `arbInList(Is)` _is equal to_ a (fixed)
integer not in `Is`.

### Frontend Syntax

We do not need special frontend syntax to define `arb()`.
We only need to define it in the usual way as a function
(instead of a language construct), and provide no axioms for it
(the `(Function)` axiom is generated automatically from the `function`
attribute annotation).

W.r.t. the `arb` variants, we can use `?` variables and the `function`
annotation to signal that the defining rules should be Skolemized when
kompiled to KORE ([see below](#skolemization)) for the defining rules.
For example, `arbInList` could be defined in K as

```
syntax Int ::= arbInList(List{Int}) [function]
rule arbInList(Is:List{Int}) => ?I:Int
  ensures ?I inList{Int} Is
```

### Skolemization

One possible approach to implementing the above would be through
[Skolemization](https://en.wikipedia.org/wiki/Skolem_normal_form),
i.e., by replacing the existential variables with fresh uninterpreted functions
applied to the universally quantified variables.

For example, the `(ARB)` rule above could be Skolemized to

```
(ARB') \forall Is:List{Is} . arbI(Is) \in Is /\ arbInList(Is) = arbI(Is)
```
where
```
arbI : List{Int} -> Int
```

is a symbol satisfying the `(Function)` axiom, without further constraints.


We propose to implement a Skolemization compilation step triggered by a
`function` annotation in the syntax definition, together with the use of `?`
variables in the `rhs` of the rule and the `ensures`.

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
(INTERVAL) \forall M:Int . \forall N:Int .
    interval(M,N) = \exists X:Int . X:Int /\ X >= M /\ X <= N
```

### Frontend Syntax

Since expressing the axiom for `interval` requires an an existential
quantification on the right-hand-side, thus making it a non-total-function-like symbol
defined through an equation, using `?` variables might be confusing since their
usage would be different from that presented in the previous sections.

Hence, the proposal to support this would be to write this as a proper ML rule.
A possible syntax for this purpose would be:

```
eq  interval(M,N)
    ==
    #Exists X:Int .
        (X:Int #And { X >=Int M #Equals true } #And { X <=Int N #Equals true })
```

Additionally, the symbol declaration would require a special attribute to
signal the fact that it is not a constructor but a _defined_ symbol.

Since this feature is not clearly needed by K users at the moment, it is only
presented here as an example; its implementation will be postponed for such time
when its usefulness becomes apparent.
