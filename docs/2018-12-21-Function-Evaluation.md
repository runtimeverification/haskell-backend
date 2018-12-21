Algorithm for function evaluation
=================================

Problem
-------

When doing normal execution, it is natural to evaluate functions immediately
after applying a rule, when simplifying the result. However, this does not
always work when doing symbolic execution because recursive functions may
be expanded indefinitely.

As an example, if the length of a list is defined as

```
len(Nil) = 0
len(Cons(_, X)) = 1 + len(X)
```

then, if `Y` is a symbolic variable and we try to evaluate `len(Y)`, we can
expand it to the infinite sequence

```
0 and Y = Nil
1 and Y = Cons(Y1, Nil)
2 and Y = Cons(Y1, Cons(Y2, Nil))
...
```

Partial solution
----------------

We will separate functions into safe functions, unsafe but acceptable functions,
and complicated functions.

First, a symbol is constructor-like if it is a constructor, a sort injection,
or a "constructor modulo axioms" like Map.concat and Map.elem
(not defined precisely here).

### Safe functions

A function is safe if evaluates (including the predicate) to either

1. patterns without free variables
1. patterns whose symbols are constructor-like
1. patterns whose symbols are either constructor-like or functions which
   are safe according to this definition.

### Acceptable functions

A function is acceptable if evaluates (including the predicate) to either

1. patterns without free variables
1. patterns whose symbols are constructor-like
1. patterns whose terms have constructor-like symbols at the top
1. patterns whose symbols are either constructor-like or functions which
   are safe according to this definition.

### Complicated fuctions

A function is complicated if it is not acceptable.

### Safe evaluation results

1. Any result which we get without having a substitution/predicate `X=p`
   where `X` is a symbolic variable and `p` contains axiom variables, but it's
   not itself a variable, is safe.
1. Any result whose symbols are either constructor-like or safe functions
   is safe.

### Acceptable evaluation results

1. Any safe result is also acceptable.
1. Any result whose symbols are either constructors-like or
   acceptable functions, is acceptable.
1. Any result whose term has a constructor-like symbol at the top is acceptable.

### Function evaluation

1. Any function application that evaluates to safe results is evaluated at
   simplification time.
1. Any function application that evaluates to acceptable results is
   evaluated at unification/matching time whenever we try to unify
   two symbol applications and the result would be of the form
   `safe-results vs acceptable-results`. We keep evaluating symbol applications
   at the top of terms in the two result sets (if any) until either they
   have a constructor-like symbol at the top or they have no symbol at the top
   (e.g. top/bottom).

Evaluating any other function applications (e.g. containing unsafe results)
is not explored here. We may try to print an error, or we may try to do the
expansion mentioned above, hoping that it will work.

As an example, we are still not able to evaluate `len(Y)` where `len`
is the function defined above. Note that the function becomes acceptable
if we use Peano arithemtic, with `Succ` and `Zero` as constructors. Also,
we could add the constraint `forall Z . len(Z) >= 0`, which would make it
evaluable in contexts where the SMT can stop the infinite expansion,
e.g. `10=len(Y)`.
