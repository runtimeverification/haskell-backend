# Tests for simplification in `booster` (executed with `booster-dev` only)

This integration test runs a few simplification requests with `Int`
expressions. It is expected that known rules from `domains.md` apply,
which will, e.g., move symbolic terms in additions and subtractions to
the left.

Since `booster-dev` is used without an llvm backend library, no
integer evaluation is expected in the results.

Some additional functions and predicates were defined to test the
behaviour for recursive evaluation (when an evaluation or
simplification has a requirement which must be simplified/evaluated
before it is found to be true). See `simplify.k` for details.

* Integer evaluation and simplification

  | Name                      | Input             | Expected output   | rules in `domains.md` which |
  |-------------------------- | ----------------- | ----------------- |---------------------------- |
  | _no-simplification_       | `123`             | `123`             | n/a                         |
  | _plus-null-removed_       | `0 + f(34)`       | `f(34)`           | remove the zero addition    |
  | _symbolic-first_          | `12 + f(34)`      | `f(34) + 12`      | move symbolic values left   |
  | _symbolic-first-of-3_     | `12 + f(34) + 56` | `f(34) + 12 + 56` | move symbolic values left   |
  | _evaluate-under-function_ | `f(12 + 0)`       | `f(12)`           | remove the zero addition    |

  - _with-logging_ is the same as _symbolic-first-of-3_ but with simplification logging enabled.


* Recursive evaluation of equation constraints

  | Name                      | Input    | Expected output | because                               |
  |-------------------------- | -------- | --------------- |-------------------------------------- |
  | _evaluate-two-stage-fail_ | `g(2)`   | `g(2)`          | no evaluation rule applies            |
  | _evaluate-two-stage_      | `g(1)`   | `1`             | applying rule `eval-g`                |
  |                           |          |                 | after evaluating `p3(1)` to `true`    |
  | _simplification-loop_     | `p1(42)` | `p1(42)`        | simplification attempt detects a loop |
  |                           |          |                 | and returns the original              |

  - **The _simplification_loop_ test loops forever in `kore-rpc-booster` and `kore-rpc-dev`.**

* Tests for the `#if-#then-#else` hook

  | Name                         | Input (paraphrased)                    | Expected output |
  |----------------------------- | -------------------------------------- | --------------- |
  | _if-then-else-true_          | `#if true #then 1 #else 0 #fi`         |  `1`            |
  | _if-then-else-false_         | `#if false #then 1 #else 0 #fi`        |  `0`            |
  | _if-then-else-eval_          | `#if (false => X) #then 1 #else 0 #fi` |  `1`            |
  | _if-then-else-indeterminate_ | `#if true #then 1 #else 0 #fi`         |  `1`            |
  | _if-then-else-sort-error_    | `#if 42 #then 1 #else 0 #fi`           | _Error (sort)_  |
  | _if-then-else-arity-error_   | `#if_#then_#else(true, 0)`             | _Error (arity)_ |
