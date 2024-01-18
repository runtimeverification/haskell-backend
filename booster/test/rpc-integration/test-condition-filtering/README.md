# Tests to check whether syntactic condition filtering works

These tests should be executed with `booster-dev --no-smt` to ensure
that the filtering is indeed _syntactic_.

### Configuration and rules in the [definition](../resources/condition-filtering.k)
  * `State` sort: `S1()`, `S2()`, or `S3()`
  * Configuration: `<k>$PGM:State</k><x>0:Int</x>`
  * Paraphrased rules
    - `S1 => S2 requires X == 0`
    - `S1 => S3 requires X /= 0`
    - `S2 => S3 requires p(X)` for an opaque predicate `p`
  * Simplification: `X ==Int X => true` (since no LLVM library is provided)

### Tests and expectations

Each test will execute a single step (as per parameter file).

| Name             | State | x   | Constraint      | with `booster-dev --no-smt` | Remark               |
|------------------|-------|-----|-----------------|-----------------------------|----------------------|
| `s2x-and-px`     | `S2`  | `X` | `p(X)`          | `(S3,X)` with `p(X)`        | relies on filtering  |
| `s1x-and-x-is-0` | `S1`  | `X` | `#Equals(X, 0)` | `(S2, 0)` with subst `X==0` | substitution prior   |
|                  |       |     |                 |                             | to processing        |
| `s1-X0`          | `S1`  | `0` | -               | `(S2, X)`                   | ==Int simplification |
