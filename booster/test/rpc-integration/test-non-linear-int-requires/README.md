This test is useful for debugging the SMT solver retry logic. To force the solver to return unknown and retry, run the server with a very short SMT timeout, e.g. `booster-dev --smt-timeout 1`.

Note that with the changes [PR#3960](https://github.com/runtimeverification/haskell-backend/pull/3960) is merged, Booster starts assuming indeterminate rewrite rule conditions and going on rewriting, hence this test will always make a rewrite step.
