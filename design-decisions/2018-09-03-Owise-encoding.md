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

Decision
--------

Encode the axiom as:

```
f(t1(x1, ..., xj), ..., tk(x1, ..., xj))
    = T(x1, ..., xj)
    if And(
        P(x1, ..., xj)
        Not(
            Or{i = 1, n}(
                exists xi1 . exist xi2 . ... exists xi_ji (
                    And(
                        And{p = 1, k}(
                            Ceil(And(ti_p(xi1, ..., xi_ji), tp(x1, ..., xj)))
                        )
                        Pi(xi1, ..., xi_ji)
                    )
                )
            )
        )
    )
```

Note that only the `x1, ..., xj` variables are (implicitly) quantified
universally here, while all the other variables have existential quantifiers.

Equals vs And explanation
-------------------------

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