# Changelog

All notable changes to this project will be documented in this file.

## Unreleased

### Added

### Changed

### Deprecated

### Removed

### Fixed

- `kore-exec` exits with the code specified by the semantics, even when the
  final configuration has side conditions.

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
