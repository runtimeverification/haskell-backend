# Changelog

All notable changes to this project will be documented in this file.

## Unreleased

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

### Removed

- Removed options for debugging equation application:
  - `--debug-applied-rule`
  - `--debug-simplification-axiom`
  - `--debug-simplification-axiom-patterns`
- Removed log entry types:
  - `DebugAppliedRule`
  - `DebugAxiomEvaluation`
  - `DebugSkipSimplification`

## [0.1.0] - 2018-01-17

### Added

- Initial release of the Kore Haskell parser.
