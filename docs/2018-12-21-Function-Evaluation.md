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

A function is safe if

1. The function is builtin and does not have axioms for non-builtin evaluation
   (e.g. `+Int`, but not `bitRangeInt` for the EVM semantics since it also has a
   non-builtin definition).
1. The function evaluates (including the predicate) to either
    * patterns without free variables (i.e. constant functions)
    * patterns whose symbols are constructor-like
      (including `Map.concat and kseq`)
    * patterns whose symbols are either constructor-like or functions which
      are safe according to this definition.

Examples:
* `+Int`, `.Map`
* `id(x) := x`
* `succ(x) := x +Int 1`
* `bitRangeInt` for the EVM semantics since it evaluates to safe functions.
* `initStateCell` where `initStateCell(.KList)=>'<state>'('.Map'(.KList))`
  since it evaluates to patterns with constructor-like symbols.
* `initTCell` where
  `initTCell(Init)=>'<T>'(initKCell(Init),initStateCell(.KList))`
  (assuming that `initKCell` is also safe) since it evaluates to
  since it evaluates to patterns with constructor-like symbols and safe
  symbols.

### Acceptable functions

A function is acceptable if
1. The function is builtin and does not have axioms for non-builtin evaluation
1. The function evaluates (including the predicate) to either
    * patterns without free variables
    * patterns whose symbols are constructor-like
    * patterns whose terms have constructor-like symbols at the top
    * patterns whose symbols are either constructor-like or functions which
      are safe according to this definition.

Examples:
1. all safe functions are acceptable
1. `plus` for Peano arithmetic where `plus(s(x), y) = s(plus(x, y))` and
  `plus(0, y) = y`.
    * Unsafe because it is not builtin, and it evaluates to a pattern
      which contains `plus`, so it does not fit the second part of the
      safe function definition.
    * Acceptable because the result has a constructor at the top.
1. `parseHexBytes` from the erc20 verification semantics, where
    * `parseHexBytes("") = .WordStack`
    * `parseHexBytes(S) = :Int_WordStack(parseHexWord(substr(S, 0, 2)), parseHexBytes(substr(2, len(s)))) if len(S) >= 2`
    * Unsafe for the same reason as `plus`.
    * Acceptable because, on both branches, the result has a constructor at the
      top

### Complicated functions

A function is complicated if it is not acceptable.

Examples:
1. The `len` function defined above.
    * Not acceptable because `1 +Int len(x)` has `+Int` at the top, which
      is not a constructor, and it does not contain only
      constructors and acceptable functions (i.e. it contains `len`).


### Safe evaluation results

`f(...)` evaluates to a safe result if any of the following is true
1. The evaluation process does not add, to the
   substitution/predicate, the following:
    * substitutions `X=p` where `X` is a symbolic variable
      and `p` contains axiom variables, but it's
      not itself a variable
      (`x=constant` and `x=y` are fine, `x=f(y)` is not fine). Note that
      `x=y` should not occur in practice, since we would actually use it as
      `y=x`, i.e. `normal-variable=symbolic-variable`.
1. The result's symbols symbols are either constructor-like or safe functions
   (both in the term and the predicate).

Examples:

The following are safe:
1. evaluating something to `2 and []`
   since the predicate/substitution is empty.
1. evaluating something to `x +Int y and []`
   since the predicate/substitution is empty.
1. evaluating something to `f(x) and [y=3]`
   since `3` does not contain variables.
1. evaluating something to `f(x) and [y=z]`
   since `z` is a variable.
1. evaluating `plus(s(s(0)), y)` to `s(plus(s(0), y))` with the rule above
   since we're not adding anything to the substitution/predicate.

The following are not safe:
1. evaluating `plus(x, y)` with the axiom
   `plus(s(x'), y') = s(plus(x', y'))`
   since we would use `x=s(x')` in the substitution and the result uses
   an unsafe function, i.e. `plus`
1. evaluating `parseHexBytes(x)` with the second axiom above since
   the result contains `parseHexBytes`, which is not safe

### Acceptable evaluation results

1. Any safe result is also acceptable.
1. Any result whose term symbols are either constructors-like or
   acceptable functions, is acceptable.
1. Any result whose term has a constructor-like symbol at the top is acceptable.

Examples:

The following are acceptable:
1. evaluating `plus(x, y)` to `s(plus(z, y)) and [x=s(z)]`
   since the term `s(plus(z, y))` has a constructor at the top.
1. evaluating `parseHexBytes(x)` with the second axiom above
   since the term has a constructor at the top.
1. evaluating `len(X)` if `len` would be defined over Peano integers,
   i.e. `len(Cons(_, X)) = s(len(X))`,
   since the term has a constructor at the top.

The following is not acceptable:
1. evaluating `len(X)` to `1 +Int len(Y) and [X=Cons(_, Y)]` since `+Int`
   is not a constructor and `len` is not acceptable.

### Function evaluation

1. Any function application that evaluates to safe results is evaluated at
   simplification time.
1. Some function applications that evaluate to acceptable results are
   evaluated at unification/matching time.
   To be specific, whenever we try to unify `sigma(s1..sn)` with `tau(t1..tn)`
   and `sigma(s1..sn)` is a safe result, or can be evaluated to one
   and `tau(t1..tn)` is an acceptable result or can be evaluated to one
   (or the other way around), we evaluate both of them until they
   can't be further evaluated, or both are constructor-like, or have
   constructor-like symbols at the top.

Evaluating any other function applications (e.g. containing unsafe results)
is not explored here. We may try to print an error, or we may try to do the
expansion mentioned above, hoping that it will work.

As an example, we are still not able to evaluate `len(Y)` where `len`
is the function defined above. Note that the function becomes acceptable
if we use Peano arithemtic, with `Succ` and `Zero` as constructors. Also,
we could add the constraint `forall Z . len(Z) >= 0`, which would make it
evaluable in contexts where the SMT can stop the infinite expansion,
e.g. `10=len(Y)`.
