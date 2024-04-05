# Testing `get-model`

Tests `get-model` requests. Many of these tests were [replicated from the `haskell-backend`](https://github.com/runtimeverification/haskell-backend/tree/master/test/rpc-server/get-model) test suite without modifications.

* an input without a predicate:
  - Input kore term: `\and(notBool(X:SortBool), X:SortBool)` , interpreted as a _term_, not as a predicate. Therefore, the input does not have any predicate, and the server returns an indeterminate result.
  - Result: `unknown`
* a non-satisfiable predicate
  - Input: `X >= 10 && X < 5`
  - Result: `unsat`
* a non-satisfiable predicate with variables (terms)
  - Input kore term: `\equals(notBool(X:SortBool), X:SortBool)`
  - Result: `unsat`
* satisfiable predicates
  - Input: `X <= 10 && X < 5`
  - Result: `sat`, substitution `X = 0`
* a trivial satisfiable predicate without variables
  - Input kore term: ` 0 <= 0`
  - Result: `sat`, no substitution
* a predicate that causes the SMT solver to return `Unknown`
  - Input kore term: `X == X ^ 256`
  - Result: `unknown`, no substitution

Tests involving variables that cannot be back-translated

* `with-map`: satisfiable predicate involving an irrelevant `Map` lookup
  - Input predicates:
    - `Map.lookup(?STORAGE, KEY) < Map.lookup(?STORAGE, KEY) + AMOUNT`
    - `KEY <= 42`
    - `AMOUNT <= 1`
  - Result: `sat`, substitution `AMOUNT = 1, KEY = 0, ?STORAGE = ?STORAGE`
    (the latter irrelevant but present)
* `with-map-unsat`: unsatisfiable predicate involving an irrelevant `Map` lookup
  - Input predicates:
    - `Map.lookup(?STORAGE, KEY) < Map.lookup(?STORAGE, KEY) + AMOUNT`
    - `KEY <= 42`
    - `AMOUNT < 1`
  - Result: `unsat`, no substitution
* `with-map-relevant`: predicate involving a relevant `Map` lookup
  - Input predicates:
    - `AMOUNT < Map.lookup(?STORAGE, KEY)`
    - `KEY <= 42`
    - `AMOUNT <= 1`
  - Result: `sat`, substitution `AMOUNT = 0, KEY = 0, ?STORAGE = ?STORAGE`.
    (NB: `?STORAGE` value is relevant but not provided)
* `with-map-unsat2`: unsatisfiable predicate with a relevant `Map` lookup
  - Input predicates:
    - `Map.lookup(?STORAGE, KEY) < Map.lookup(?STORAGE, KEY)`
    - `KEY <= 42`
  - Result: `unsat`, no substitution
