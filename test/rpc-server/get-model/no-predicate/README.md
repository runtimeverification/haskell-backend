# `get-model` applied to an input without a predicate

* Input kore term: `\and(\not(X:SortBool), X:SortBool)`
* Result: `satisfiability-unknown`

The input is interpreted as a _term_, not as a predicate. Therefore,
the input does not have any predicate, and the server returns an
indeterminate result.
