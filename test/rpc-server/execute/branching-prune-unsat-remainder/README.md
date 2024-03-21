# Pruning an unreachable remainder branch

The definition `test.k` contains two rewrite rules with complementary side condition, i.e.
the conjunction of these conditions is `true`.

The configuration contains the term `a ( I:Int , f ( I:Int ) )`, for which both rules unify.

Prior to [PR #3745](https://github.com/runtimeverification/haskell-backend/pull/3745), `kore-rpc` would attempt to explore the third branch, induced by the remainder condition of the two rules. In this case, it is obvious that the remainder branch is unreachable, as the negation of the conjunction of the two rules' side conditions is `false`. The backend, however, optimistically dives into the remainder branch and start to evaluate `f(I)`, which loops forever.

The solution is to prune the remainder branch early, based solely on the remainder predicate, i.e. without simplifyi the configuration under under the assumption of a possibly unsatisfiable condition. This integration test makes sure we do that.
