# Product Guidelines — Haskell Backend

## Tone & Documentation Style

- **Pragmatic engineering:** Clear, concise, and practical. Write for contributors who need to understand and modify the code efficiently.
- Avoid unnecessary formality. Explain the "why" behind non-obvious decisions; skip obvious boilerplate documentation.
- Document public APIs, complex algorithms, and architectural boundaries. Let well-structured code speak for itself elsewhere.

## Architectural Direction

- **Booster-first:** The `booster` package is the reference implementation and the future of this project. All new development should follow booster's patterns, module structure, and abstractions.
- The original `kore` backend is being gradually phased out. New features and improvements should target `booster`, not `kore`.
- When modifying shared components (e.g., `kore-rpc-types`), ensure changes are driven by booster's needs and do not introduce unnecessary coupling with legacy kore patterns.

## Code Conventions

- **Follow booster's Haskell idioms:** Leverage the GHC extensions enabled in the project (GADTs, DerivingVia, OverloadedStrings, OverloadedRecordDot, etc.). Prefer type-safe patterns, explicit qualified imports, and clear data type definitions.
- **Respect package boundaries:** The monorepo has four packages (`kore`, `booster`, `kore-rpc-types`, `dev-tools`). Minimize cross-package coupling. The `kore-rpc-types` package defines the shared interface — keep it lean.
- **Formatting is non-negotiable:** All Haskell code must pass `fourmolu` and `hlint`. CI enforces this as a hard gate. Run `nix develop .#style --command scripts/fourmolu.sh` before submitting changes.

## Testing

- Integration tests use the JSON RPC protocol with Python's `jsonrpcclient`.
- Performance regressions are tracked via downstream test suites (KEVM, Kontrol). Include performance timings in PRs that affect the rewriting engine.
- Unit tests use the Tasty framework.

## Commit & Review Standards

- Keep commits focused and atomic.
- PR descriptions should explain the motivation and impact, especially for changes that affect rewriting semantics or performance.
