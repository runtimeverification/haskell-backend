# Changelog

All notable changes to this project will be documented in this file.

## Unreleased

### Added

### Changed

### Deprecated

### Removed

### Fixed

## [0.49.0.0] - 2021-06-30

### Added

- Added option to output logs in one-line format (#2596).
- Improved performance of simplification (#2520).

### Fixed

- Fixed issue with `unifyStringEq` (#2586).

## [0.48.0.0] - 2021-06-16

### Added

- Adds support for Z3's `:rlimit` with `--smt-rlimit` CL option (#2407).
- Enables building with `-eventlog` by default (#2658).
- Adds option `--not-matching-children` to `kore-prof` (#2631).

### Fixed

- The `SideCondition.andCondition` performance regression is fixed (#2454).
- Decoding bytes is improved (fixes added in relation to #2591).

## [0.47.0.0] - 2021-06-02

### Added

- The hook `KEQUALS.neq` eagerly returns `false` when two symbolic patterns are
  equal. (#2634)
- The hooks `BYTES.decodeBytes` and `BYTES.encodeBytes` are implemented. (#2619)
- The warning `WarnIfLowProductivity` indicates the definition where the warning
  occurred. (#2594)
- `kore-repl` records effect-ful commands from the current session when it
  saves a bug report. (#2614)

### Fixed

- The definitions of functions in `prelude.kore` are rewritten in the format
  expected by the LLVM backend. (#2629)
- `\next` is correctly distributed over `\or` during simplification. (#2608)

## [0.45.0.0] - 2021-05-10

### Fixed

- The hook `STRING.string2base` remains unevaluated where it is not implemented.
  (#2546)
- The backend no longer crashes when it unparses internal representations of
  certain terms. (#2494)
- The backend no longer crashes when it rewrites with a rule where the
  right-hand side is `\bottom`. (#2561)
- The backend accepts groups of equations containing `owise` rules. (#2523)

## [0.44.0.0] - 2021-04-22

### Fixed

- Concrete side conditions will be fully simplified. (#2526)
- A memory leak is removed where deciding if a Map or Set is defined. (#2550)

## [0.43.0.0] - 2021-04-07

### Changed

- `kore-repl` displays error messages in a user-friendly format. (#2514)

### Fixed

- Several performance regressions are fixed. (#2504, #2510)
- The backend does not report an error when unifying a Set- or Map-valued
  function with another term. (#2493)

## [0.42.0.0] - 2021-03-17

### Added

- `kore-repl` accepts the `--bug-report` and `--no-bug-report` options. (#2462)

### Changed

- Apply user-defined equations as written, instead of simplifying the left-hand
  side during initialization. (#2392)
- Match `#as` (`\and`) patterns correctly, instead of relying on simplifying
  them during initialization. (#2392)

### Fixed

- A performance regression related to strictness is fixed. (#2447)
- `kore-exec` distinguishes `\bottom` from stuck states, instead of reporting
  the last defined state as stuck. (#2451)
- Errors are reported on `stderr` instead of `stdout`. (#2458)
- Applying user-defined equations is more efficient. (#2438)
- `kore-exec` reports an error when any input file is missing. (#2446)

## [0.41.0.0] - 2021-03-05

### Changed

- Clauses in the side condition of a configuration are considered when
  simplifying applying equations to other clauses in the side condition (#2393).

### Fixed

- Values of the `BYTES.Bytes` sort are unparsed in the correct 8-bit encoding
  instead of the base-16 encoding. (#2411)

## [0.40.0.0] - 2021-02-17

### Fixed

- When a function equation is rejected for having the wrong form, the source
  location of the rule is displayed. (#2408)
- When a function cannot be evaluated because it was not given any rules, the
  source location of the function declaration is displayed. (#2377)
- When the proof of a reachability claim is stuck, the source location of the
  original claim is displayed. (#2377)

## [0.39.0.0] - 2021-02-04

### Added

- `kore-parser` accepts the `--pattern` argument multiple times. It will
  validate all the patterns with a single definition. (#2369)

### Changed

- `kore-exec --version` will report the version number and Git commit, but not
  the build date. The build date was never reported correctly anyway. (#2370)

### Fixed

- The priority of equations is respected again. (#2366)
- Terms are still equal if the backend has inferred that one is defined but not
  the other. (#2372)
- Uninterpreted functions appearing in the keys of maps and sets are handled
  correctly. (#2323)

## [0.38.0.0] - 2021-01-24

### Added

- Add profiling traces for rewriting and simplification during ordinary
  execution. (#2331)

### Changed

- Apply symbolic simplification rules to hook `KEQUAL.eq` under `\and` and
  `\equals`. (#2346)
- Include `result.kore` in output with `--bug-report`. (#2018)
- Predicates have a distinguished internal representation. (#2099)
- Unification problems in the argument positions of equations are solved during
  initialization. (#2326)

### Fixed

- `kore-repl` no longer reports all remaining states (after rewriting) as stuck.
  (#2335)
- The bounded model checker returns `\top` when the property holds up to the
  specified bound, but emits a warning if the bound was reached before execution
  finished. (#2342)

## [0.37.0.0] - 2021-01-07

### Added

- Added option `--no-bug-report` to suppress generation of the bug report
  archive. (#2311)
- Check the validity of SMT declarations at initialization. (#2314)

### Changed

- Removed single-quote delimiters around Kore identifiers in validation error
  messages. (#2316)
- Relaxed the check on total functions to permit functions with undefined
  arguments. (#2334)
- The `--solver-transcript` option will cause an existing log file to be
  overwritten, instead of appending to it. (#2307)

### Fixed

- Correctly check the final implication of claims where the right-hand side is
  \bottom. (#2329)

## [0.36.0.0] - 2020-12-09

### Added

- Added option `--error-entries` to turn any log entry into an error. (#2285)

### Changed

- `krun` always prints fully-simplified states. (#2299)
- `kore-exec` sends terms to the SMT solver if it can infer dynamically that
  they are defined at runtime. (#2287)
- The `kore-parser` options `--no-print-definition` and `--no-print-pattern` are
  now the default. (#2264)

### Deprecated

### Removed

### Fixed

- The performance of the parser is significantly improved. (#2189)
- `kore-parser` prints a helpful error message if the `--module` option is
  omitted where it is required. (#2254)

## [0.35.0.0] - 2020-11-30

### Added

- Added hooked function `LIST.make`. (#2253)

### Changed

- Hooked function `LIST.update` is `\bottom` for negative indices. (#2278)
- The concrete syntax of domain values in `BYTES.Bytes` matches the LLVM
  backend. (#2256)

### Fixed

- Execution with `krun` reports all stuck configurations. (#2205)
- Bug reports generated by `kore-exec` display the command-line options
  correctly. (#2245)

## [0.34.0.0] - 2020-11-16

### Added

- The `STRING.string2base` hook parses signed hexadecimal values. (#2251)
- The `\left-assoc` and `\right-assoc` notations are parsed. (#2124)
- Functional terms are translated as uninterpreted functions for the SMT solver
  if no other translation is available. (#2261)

### Fixed

- The environment variable `KORE_EXEC_OPTS` has no effect outside
  `kore-exec`. (#2235)
- Claims with an `ensures` clause does not cause an internal error. (#2221)
- The `--strategy all` option is effective. (#2205)
- The rule merger does not complain about duplicate names when there are not
  duplicate names. (#2226, #2228)
- `kore-parser` prints human-readable error messages. (#2243)

## [0.33.0.0] - 2020-10-29

### Added

- The `--solver-reset-interval` option allows the user to specify how often the
  SMT solver will be reset. (#2207)
- Conditions quantified by `\forall` are sent to the SMT solver. (#2183)

### Changed

- Failing queries to the SMT solver are retried once, after resetting the
  solver. (#2208)
- The `--save-proofs` option is always effective, even when all claims are
  successfully proven. (#2183)
- The `--strategy all` option is now the default, instead of `--strategy any`.
  (#2204)

### Removed

- The `--strategy any-heating-cooling` and `--strategy all-heating-cooling`
  options are removed. (#2204)

## [0.32.0.0] - 2020-10-15

### Changed

- `\equals` clauses are normalized by ordering their child terms. (#2137)
- The SMT solver is reset at fixed intervals. (#2125)

### Fixed

- The warning about trivial claims shows the original source location. (#2155)

## [0.31.0.0] - 2020-09-30

### Added

- Inferred conditions are used to simplify unevaluated functions. (#2095)

### Changed

- The prover infers that the right-hand sides of claims are defined. (#2110)

### Fixed

- Unsatisfiable configurations are filtered from the right-hand side of
  claims. (#2145)
- Function evaluation is disabled while matching the left-hand side of an
  equation. (#2143)

## [0.30.0.0] - 2020-09-18

### Changed

- The prover halts if the SMT solver returns `unknown`. (#2072)

### Fixed

- Function evaluation returns a result after the first equation which
  applies. (#1146)

## [0.29.0.0] - 2020-09-04

### Added

- The SMT solver transcript (`--solver-transcript`) shows reponses received from
  the solver. (#1688)

### Changed

- The internal representation of terms is simplified. (#2104)
- The prover keeps the right-hand side of its working claim simplified. (#1278)

### Fixed

- The SMT solver no longer fails to solve simple queries. (#2075)
- The SMT solver no longer leaks memory. (#2087)
- Simplifying conjunctions of predicates runs in linear time, rather than
  quadratic. (#2102)
- Proven states are not accidentally reported as "stuck". (#2021)
- The prover halts at the first unproven state. (#2071)

## [0.28.0.0] - 2020-08-19

### Added

- Add symbolic rules for `STRING.eq`. (#2014)
- Add symbolic rules for `INT.eq`. (#2019)

### Changed

- Throw an error when `\not(\ceil(_))` appears in a stuck configuration. (#2059,
  #2061)
- Produce a helpful error message when the `--smt-prelude` file is
  missing. (#2055)
- Solicit a bug report when catching `AssertionFailed`. (#2060)
- Solicit a bug report when recording `WarnIfLowProductivity`. (#2037)
- Disable the `WarnIfLowProductivity` message when total run time is
  short. (#2036)
- Allow an empty argument to the `simplification` attribute. (#2029)
- Infer that the left-hand sides of claims are defined. (#1911)

### Deprecated

### Removed

### Fixed

- Correctly re-construct the unified term when unifying `\equals(_, _)`. (#2067)
- Erase predicate sorts before sending to the SMT solver. (#2076)
- `--bug-report` captures the `--smt-prelude` file. (#2054)
- `kore-repl` does not terminate after sub-process errors. (#1992)
- Send correct command to solver to set timeout. (#2048)
- `kore-exec` no longer leaks memory. (#2028)

## [0.27.0.0] - 2020-08-05

### Added

- Add symbolic reasoning for SET.difference.
- Add SET.inclusion hook.

### Changed

- Add more context to some error messages.
- Update stack.yaml to GHC 8.10.

### Fixed

- Fix several memory leaks.
- Enable RTS statistics by default in all build configurations.
- Allow narrowing on uninterpreted functions.

## [0.26.0.0] - 2020-07-24

### Added

- Speedscope is now supported for profiling proofs.
- kore-repl can list rules applied between any related nodes.
- kore-repl allows enabling debug-equation dynamically.
- A warning is emitted to distinguish the types of proof failure.

### Fixed

- A bug is fixed where variables introduced by symbolic narrowing could be
  captured incorrectly.
- A more helpful message is provided when the external solver crashes.
- The interrupt signal no longer triggers the creation of a bug report archive
  automatically.
- The overhead of logging is significantly reduced.
- Polymorphic symbols can now be encoded for the external solver.

## [0.25.0.0] - 2020-07-08

### Added

- The `simplification` attribute takes an optional integer argument indicating
  the priority of the simplification rule.
- The hooked function `INT.ediv` implements Euclidean division.

### Changed

- `ErrorBottomTotalFunction` is thrown when a function declared total
  (`functional`) returns `\bottom`.
- `ErrorDecidePredicateUnknown` is thrown when the solver cannot decide if a
  condition is satisfiable or unsatisfiable.

### Fixed

- `kore-exec` exits with the code specified by the semantics, even when the
  final configuration has side conditions.
- `kore-exec` and `kore-repl` halt when the limit specified by the `--breadth`
  option is exceeded.
- Proofs are no longer incomplete when the final configuration is undefined.
- `kore-repl` does not allow `clear`-ing the direct child of a branching node
  because this can invalidate a proof.

## [0.24.0.0] - 2020-06-25

### Added

- The hook `INT.eq` is reflexive with symbolic arguments.
- The unification-based interpretation of function equations is supported.

### Fixed

- Improved function evaluation performance by reducing book-keeping.
- Improved unification performance by removing excess logs.
- Improved execution performance by discarding historical configurations.
- `kore-repl` respects all logging options.

## [0.23.0.0] - 2020-06-10

### Added

- `kore-exec` and `kore-repl` save the information necessary to reproduce a bug
  with the option `--bug-report`.
- The hook `BOOL.or` is simplified to `\and` when possible.
- The hook `SET.in` is simplified to `\and` when possible.

### Fixed

- The error message thrown when a rewrite rule cannot be instantiated uses
  variable names consistently.

## [0.22.0.0] - 2020-05-27

### Added

- A warning is emitted when a total function returns `\bottom`.

### Changed

- Execution does not branch when evaluating the hooked `KEQUAL.eq` function.

### Fixed

- Overloaded symbols are now correctly unified with injected variables.
- Error messages are no longer duplicated in the log.

## [0.21.0.0] - 2020-05-13

### Added

- Injections into hooked sorts are forbidden.
- Semantic rules with the same left- and right-hand sides will be rejected.
  Such rules will always cause the backend to loop endlessly.
- `kore-repl` prints output in script mode with the option `--save-run-output`.

### Changed

- kore-repl: `stepf` command advances the current configuration.
- `kore-exec` does not retain the interior of the execution graph.
  Only the leaf nodes of the execution graph are retained during
  execution. Memory use is bounded by the size of the largest configuration and
  does not increase with the length of the proof.
- Applying semantic (rewrite) rules is more efficient.
  Run time is improved 10-15% by avoiding duplicate work when refreshing the
  free variables of semantic rules.

## [0.20.0.0] - 2020-04-29

### Added

- Added documentation for the `--log-entries` option.

### Changed

- Clarified the message accompanying the "substitution coverage" error.

### Fixed

- The `smtlib` and `smt-hook` attributes handle SMT-LIB lists correctly.
  The argument of these attributes would not be instantiated correctly if it was
  a list, but SMT-LIB atoms were always handled correctly.

## [0.19.0.0] - 2020-04-15

### Added

- Added options for debugging equation application:
  - `--debug-attempt-equation`
  - `--debug-apply-equation`
  - `--debug-equation`
- Added log entry types:
  - `DebugApplyEquation`
  - `DebugAttemptEquation`

### Changed

- Applying equation-based rules (primarily function rules and simplification rules) is more efficient.
- Equations may not have free variables occurring only on the right-hand side.
- Command-line options that expect a module name check that their argument is a _valid_ module name.
- The log displays the context of each entry.
- The log displays the _type_ of each context to be used with option `--log-entries` for more information.
- The format of parsing and validation errors is more similar to other parsers and compilers.

### Removed

- Removed options for debugging equation application:
  - `--debug-applied-rule`
  - `--debug-simplification-axiom`
  - `--debug-simplification-axiom-patterns`
- Removed log entry types:
  - `DebugAppliedRule`
  - `DebugAxiomEvaluation`
  - `DebugSkipSimplification`

## [0.0.1.0] - 2018-01-17

### Added

- Initial release of the Kore Haskell parser.
