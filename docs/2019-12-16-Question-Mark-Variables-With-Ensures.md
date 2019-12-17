This design document describes four typical example language constructs or mathematical functions that have unspecified or nondeterministic behaviors and shows their axiomatization in Kore. We also propose the corresponding K frontend syntax to define some of these behaviors. The frontend syntax uses question mark variables `?X`, which when translated to Kore axioms become existentially quantified, and use `ensures` to specify the logical constraints that `?X` should satisfy. The `ensures` clause will be translated to the RHS in Kore axioms. 

## Example A: Random Number Construct `rand()`

The random number construct `rand()` is a language construct. It is part of the syntax of the PL:

```
Stmt ::= "rand" "(" ")"
```

### Axioms

The intended semantics of `rand()` is that it can rewrite to every integers. Here is its axiom

```
(RAND) \forall I:Int . rand() -> * I
// equivalent form(s)
//     rand() -> \forall I:Int . * I
//     rand() -> * I
// non-equivalent form(s)
//     rand() -> * (\forall I:Int . I)
```

Note that `(RAND)` axiom is logically equivalent to the following infinitely many axioms

```
(RAND0)  rand() -> * 0
(RAND1)  rand() -> * 1
(RAND2)  rand() -> * 2
  ...    ...
(RAND-1) rand() -> * (-1)
(RAND-2) rand() -> * (-2)
  ...    ...
```

It is not easy to define many of the variants of `rand()`. For example. `randPrime()` can rewrite to every _prime numbers_. Here is its axiom

```
(RANDPRIME) \forall P:Int . isPrime(P) -> (randPrime() -> * P)
// equivalent form(s)
//          \forall P:Int . (randPrime() /\ isPrime(P)) -> *P
//          \forall P:Int . randPrime() -> (isPrime(P) -> * P)
//          randPrime() -> \forall P:Int . (isPrime(P) -> * P)
//          remove \forall P:Int in all above three
```

where `isPrime(_)` is a predicate that can be defined in the usual way. 

As another example, `randDifferentFromList(Is)` takes a list `Is` of integers and can rewrite to every integers that are not in `Is`. Here is its axiom

```
(RANDLIST) \forall Is:List{Int} . \forall I:Int . \neg(I \in Is) -> randDifferentFromList(Is) -> * I
```

### Frontend Syntax

We do not have a frontend syntax proposal for `rand()` and its variants. This is left as future work. 

## Example B: Fresh Integer Construct `fresh(Is)`

The fresh integer construct `fresh(Is)` is a language construct and part of the PL syntax

```
Stmt ::= ... | "fresh" "(" List{Int} ")"
```

### Axioms

The intended semantics of `fresh(Is)` is that it can rewrite to any integers that are not in `Is`.  

Note that `fresh(Is)` and `randDifferentFromList(Is)` are different; the former does not need to rewrite to _every_ integers not in `Is`, while the latter requires so. For example, it is _correct_ to implement `fresh(Is)` so it always returns the smallest positive integers that are not in `Is`, but same implementation for `randDifferentFromList(Is)` is considered _incorrect_. In other words, there exist multiple correct implementations of `fresh(Is)`, some of which may be deterministic, but there only exists a unique implementation of `randDifferentFromList(Is)`. Finally, it is a _correct_ if one implements `fresh(Is)` the same as `randDifferentFromList(Is)`. 

Here is the axiom of `fresh(Is)`

```
(FRESH) \forall Is:List{Int} . \exists I:Int . \neg( I \in Is) /\ (fresh(Is) -> * I)
// equivalent form(s)
//why?  \forall Is:List{Int} . fresh(Is) -> \exists I:Int . \neg( I \in Is) /\ * I
//      \forall Is:List{Int} . fresh(Is) -> \exists I:Int . * (\neg( I \in Is) /\ I)
```

### Frontend Syntax

We use the following K syntax to define `fresh(Is)`

```
rule fresh(Is:List{Int}) => ?I:Int ensures notBool(?I in Is)
```

## Example C: Arbitrary Number (Unspecific Function) `arb()`

The function `abr()` is not a PL construct, but a mathematical function. Therefore, its axioms do not use rewrites but equalities. 

### Axioms

The intended semantics of `arb()` is that it is an unspecified nullary function. The exact return value of `arb()` is unspecified in the semantics but up to the implementations. However, being a mathematical function, `arb()` must return the same value in any one implementation. 

The axiom of `arb()` is 

```
(ARB) \exists I:Int . arb() = I
//    this is exactly (Function) axiom
//    this is not equivalent to
//      arv() = (\exists I:Int . I)
```

There are many variants of `arb()`. For example. `arbDifferentFromList(Is)` is an unspecific function whose return value must be different than those in `Is`. Here is its axiom

```
(ARBDIFF) \forall Is:List{Is} . \exists I:Int . \neg(I \in Is) /\ arbDifferentFromList(Is) = I
```

### Frontend Syntax

We do not need special frontend syntax to define `arb()`. We only need to define it in the usual way as a function (instead of a language construct). 

We do not have a frontend syntax proposal to define the variants of `arb()`, such as `arbDifferentFromList(Is)` in the above. 

## Example D: Interval (Non-function Symbols) `interval()`

The symbol `interval(M,N)` is not a PL construct, but a mathematical symbol. Its axioms will not use rewrites but equalities. 

### Axioms

The intended semantics of `interval(M,N)` is that it equals the _set_ of integers that are larger than or equal to `M` and smaller than or equal to `N`. Its axiom is

```
(INTERVAL) \forall M:Int . \forall N:Int . interval(M,N) = \exists X:Int . X:Int /\ X >= M /\ X <= N
```

### Frontend Syntax

```
eq interval(M:Int,N:Int) = ?X ensures ?X >=Int M andBool ?X <=Int N
```

