# Testing `get-model`

For the time being, this is testing the pass-through of `get-model` requests to the `kore-rpc`. At the time of writing, all tests are [replicated from `haskell-backend`](https://github.com/runtimeverification/haskell-backend/tree/master/test/rpc-server/get-model) test suite without modifications.

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
