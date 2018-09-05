Owise encoding
==============

Background
----------

K allows defining functions with a default case.
A generic function definition would have multiple cases defined like this
(not using actual K syntax):

```
f(ti1(xi1, ..., xi_ji), ..., ti_k(xi1, ..., xi_ji))
    = Ti(xi1, ..., xi_ji)
    if Pi(xi1, ..., xi_ji)
```

and it would have one default (`owise`) case that looks like this:

```
f(t1(x1, ..., xj), ..., tk(x1, ..., xj))
    = T(x1, ..., xj)
    if P(x1, ..., xj) [owise]
```

Note that all the above variables have implicit universal quantifiers.

Current encoding
-----------------

This is roughly encoded as

```
f(t1(x1, ..., xj), ..., tk(x1, ..., xj))
    = T(x1, ..., xj)
    if And(
        Not(
            Or{i=1, n} (
                Ceil(
                    exists xi1 . exist xi2 . ... exists xi_ji (
                        And(
                            Pi(xi1, ..., xi_ji)
                            f(ti1(xi1, ..., xi_ji), ..., ti_k(xi1, ..., xi_ji))
                        )
                    )
                )
            )
        )
        P(x1, ..., xj)
    )
```

Note that the `Ceil` term in the `Or` is almost always `top` (if it isn't then
it's likely that there is an error in the function definition), so the `Not`
term evaluates to `bottom`, so the entire condition evaluates to `bottom`.

Decision
--------

Encode the axiom as:

```
f(t1(x1, ..., xj), ..., tk(x1, ..., xj))
    = T(x1, ..., xj)
    if And(
        Not(
            Or{i = 1, n}(
                exists xi1 . exist xi2 . ... exists xi_ji (
                    And(
                        Pi(xi1, ..., xi_ji)
                        And{p = 1, k}(
                            Ceil(
                                And(ti_p(xi1, ..., xi_ji), tp(x1, ..., xj))
                            )
                        )
                    )
                )
            )
        )
        P(x1, ..., xj)
    )
```

Note that, as in the current encoding, only the `x1, ..., xj` variables are
(implicitly) quantified universally here, while all the other variables have
existential quantifiers.

There are two changes from the current encoding:
1. There is no `Ceil` on top of the `exists` term, which becomes a direct
   child of `Or`
1. The first term of the `And` inside `exists` changed from
   ```
   f(ti_1(xi1, ..., xi_ji), ..., ti_k(xi1, ..., xi_ji))
   ```
   to
   ```
   And{p = 1, k}(
       Ceil(
           And(ti_p(xi1, ..., xi_ji), tp(x1, ..., xj))
       )
   )
   ```

Equals vs And explanation
-------------------------

One may be tempted to use `Equals(ti_p(xi1, ..., xi_ji), tp(x1, ..., xj))`
instead of `And(ti_p(xi1, ..., xi_ji), tp(x1, ..., xj))`. However, that does
not work.

Let us say that we have a function `f` of one argument and a non-functional
constructor `C` also of one argument. Let us say that our function is defined
as

```
f(C(x)) = 3
f(x) = 7 owise
```

Encoding the owise rule as
```
f(x) = 7 if not (exist y . x = C(y))
```
would fail since `x=C(y)` would always evaluate to false, so the entire
condition would always evaluate to true.

Therefore, we have to encode the rule as
```
f(x) = 7 if not (exist y . ceil(x and C(y)))
```