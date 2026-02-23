# Tech Stack — Haskell Backend

## Language & Compiler

- **Haskell** (GHC 9.6.x)
- Stack resolver: LTS-22.23
- Extensive use of GHC extensions: GADTs, DerivingVia, OverloadedStrings, OverloadedRecordDot, TypeFamilies, ScopedTypeVariables, and others

## Build Tools

- **Stack** — Primary build tool, source of truth for the Haskell package set
- **Cabal** — Alternative build path, used within Nix dev shells
- **Hpack** — `package.yaml` files for `booster` and `dev-tools`; generates `.cabal` files
- **GNU Make** — Integration test orchestration

## Nix

- **Nix Flakes** — Reproducible builds and development environments
- `cabal2nix` for building Haskell packages within Nix
- Binary caches: `k-framework` (cachix), IOG hydra (`cache.iog.io`)
- Dev shells: `.#cabal` (building), `.#style` (formatting)

## External Dependencies

| Dependency | Purpose |
|---|---|
| **Z3** | SMT solver for constraint solving (via `smtlib-backends` / `smtlib-backends-process`) |
| **LLVM backend** | FFI-linked C library (`cbits/`) for efficient simplification of bool-sorted terms |

## Core Haskell Libraries

| Library | Purpose |
|---|---|
| `aeson` / `aeson-pretty` | JSON serialization/deserialization |
| `bytestring` / `text` | Efficient string handling |
| `containers` | Maps, sets, sequences |
| `conduit` | Streaming data processing |
| `cryptonite` | Cryptographic hashing |
| `decision-diagrams` | Decision diagram data structures |
| `monad-validate` | Validation monad |
| `fast-logger` / `auto-update` | Logging infrastructure |

## RPC Layer

- Custom **JSON-RPC** server implementing the KORE RPC protocol
- Shared types defined in `kore-rpc-types` package

## Testing

- **Tasty** — Unit test framework
- **Python 3.x + `jsonrpcclient`** — Integration tests exercising the RPC protocol
- **Downstream performance suites** — KEVM, Kontrol test suites for performance regression tracking

## Code Quality

- **Fourmolu** — Haskell code formatter (CI-enforced)
- **HLint** — Haskell linter
- **GHC flags:** `-Wall -Werror` on the `kore` package; `-Wall -Wcompat -Widentities -Wincomplete-record-updates -Wincomplete-uni-patterns -Wmissing-export-lists -Wmissing-home-modules -Wpartial-fields -Wredundant-constraints` on `booster`

## CI/CD

- **GitHub Actions** — Continuous integration workflows (`.github/workflows/`)
