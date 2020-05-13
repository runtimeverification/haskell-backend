# Changelog

All notable changes to this project will be documented in this file.

## Unreleased

### Added

### Changed

### Deprecated

### Removed

### Fixed

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
