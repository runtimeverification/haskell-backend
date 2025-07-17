Indexing Issue for Unevaluated Functions
========================================

This demonstrates a bug caused by discarding rules with non-matching index, fixed in the PR that added the test.

When an unevaluated function `f` is in an indexed position, the index of the term would have a component `TopSymbol f`, and there would not be (cannot be!) any rules with such an index.
Therefore the only rules tried would be those with index `Anything` (in that component).

* If none of these rules can be applied (which is likely in practice), the returned result is `Stuck` instead of `Aborted` (see [`test-no-evaluator` result](../test-no-evaluator/)).
* All rules tried may have lower priority than one which could apply once the function gets evaluated, leading to a wrong result ( demonstrated in this test).

Rules:
```
  rule f(A) => f(B)               // index IdxFun "f"
  rule f(B) => A                  // index IdxFun "f"

  rule [consrule]:                // index TopCon "Cons"
    <k> Cons(I) => f(I) ... </k>

  rule [Vrule]:                   // index IdxVal "A"
    <k> A => Done ... </k>

  rule [varrule]:                 // index ***
    <k> _X:Abcd => B ... </k> [owise]
```

Input: `Cons(B)`

* rewritten to `f(B)` using `consrule`, which booster then tries to rewrite.
* before the indexing fix,
  - booster would _only_ try the low-priority `varrule`;
  - this succeeds, resulting in `B`,
  - which leads to the rewrite looping with `varrule`.
* With the fixed indexes,
  - booster tries _all_ rules in priority order because `f` can evaluate to different things
  - a rewrite with `consrule` or `Vrule` aborts on an indeterminate match with `f(B)`
  - the term is simplified, evaluating `f(B) => A`
  - the subsequent rewrite succeeds for `Vrule`, producing `Done`

```
Cons(B) =rewrite=> f(B) =eval=> A =rewrite=> Done    correct
                      \
                       \=rewrite=> B [owise]    should not apply!
```
