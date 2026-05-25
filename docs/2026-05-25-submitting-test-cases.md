# Bug Reports and RPC Regression Tests

## What is a bug-report tarball?

`kore-rpc-booster` can capture a self-contained reproduction of any request sequence
as a **bug-report tarball**: a `.tar.gz` file containing the compiled `.kore` definition,
the LLVM backend kore definition, and the exact JSON-RPC request/response pairs (in
sequence order) that reproduce the issue.

This is the preferred format for reporting bugs and performance regressions. It is
self-contained: no K source, no K toolchain, and no matching K framework version is
needed to replay it.

---

## Generating a bug report (downstream projects)

Pass `--bug-report <name>` to `kore-rpc-booster` while reproducing the issue:

```sh
kore-rpc-booster definition.kore \
    --main-module MY-MODULE \
    --llvm-backend-library interpreter.so \
    --bug-report my-issue \
    [other flags]
```

Trigger the slow or broken operation through your normal client, then shut the server
down (`Ctrl-C`). The file `my-issue.tar.gz` is written to the current directory.

If `--bug-report` is omitted, a tarball named `kore-rpc-booster.tar.gz` is written
automatically on an unexpected crash (`BugReportOnError` default).

---

## Replaying a bug report quickly

The `kore-rpc-client run-tarball` subcommand starts a server, replays all requests, and
prints any mismatches:

```sh
cabal build kore-rpc-client kore-rpc-booster

kore-rpc-client run-tarball my-issue.tar.gz
```

For the LLVM library, either set `LLVM_LIB` (path to a compatible pre-built `.so`) or
`PLUGIN_DIR` (path to `blockchain-k-plugin`, used to compile the LLVM backend on the
fly). See `scripts/run-with-tarball.sh` for the full set of environment variables.

---

## Converting a tarball into a permanent regression test

Use `scripts/tarball-to-rpc-test.sh` to convert a bug-report tarball into a
`runDirectoryTest`-compatible test directory under `booster/test/rpc-integration/`:

```sh
# From the repo root:
scripts/tarball-to-rpc-test.sh path/to/my-issue.tar.gz my-issue
```

This creates:
- `booster/test/rpc-integration/resources/my-issue.kore` — Haskell backend definition
- `booster/test/rpc-integration/resources/my-issue.haskell.kore` — same (for kompile)
- `booster/test/rpc-integration/resources/my-issue.llvm.kore` — LLVM backend definition
  (if present in the tarball)
- `booster/test/rpc-integration/resources/my-issue.kompile` — script to rebuild the
  `.dylib` when `PLUGIN_DIR` is set (for tarballs using the blockchain crypto plugin)
- `booster/test/rpc-integration/test-my-issue/state-NNN.<method>` — one per request
- `booster/test/rpc-integration/test-my-issue/params-NNN.json` — extra params where
  needed (execute, add-module)
- `booster/test/rpc-integration/test-my-issue/response-NNN.json` — golden responses
  (from the original tarball run; id normalised to 1)

Then verify:

```sh
cd booster/test/rpc-integration
./runDirectoryTest.sh test-my-issue
```

If the golden responses no longer match (e.g. after intentionally changing server
behaviour), regenerate them:

```sh
./runDirectoryTest.sh test-my-issue --regenerate
```

---

## LLVM backend library

Tests that use the LLVM backend require a compiled `.dylib` (`.so` on Linux).

**Without a `.dylib`:** The server starts without `--llvm-backend-library`. Concrete
term evaluation is disabled; the test may still run, but Booster cannot evaluate LLVM
builtins and results may differ from a full run.

**With a pre-built `.dylib`:** If `resources/<name>.dylib` exists it is passed to the
server automatically. Pre-built libraries are only compatible with the glibc they were
compiled against. Libraries built inside the nix dev shell require glibc ≥ 2.38 and
**will not load** when `kore-rpc-booster` was compiled against the system glibc
(Ubuntu 22.04 has 2.35).

**Rebuilding the `.dylib` locally:** Run the `.kompile` script from inside `resources/`
with `PLUGIN_DIR` pointing to `blockchain-k-plugin`. The easiest way is inside the
K integration nix shell:

```sh
nix develop github:runtimeverification/k/v$(cat deps/k_release)#kore-integration-tests \
    --override-input haskell-backend . --update-input haskell-backend

export PLUGIN_DIR=$(nix build .#blockchain-k-plugin --no-link --print-out-paths)
cd booster/test/rpc-integration/resources
bash my-issue.kompile
```

This regenerates `my-issue.dylib` and `my-issue.kore`.

---

## File-naming reference for test directories

| File | Sent as | Notes |
|------|---------|-------|
| `state-NAME.simplify` | `simplify` request; content is KoreJson state | `params-NAME.json` optional |
| `state-NAME.execute` | `execute` request; content is KoreJson state | `params-NAME.json` optional (e.g. `max-depth`) |
| `state-NAME.add-module` | `add-module`; content is raw Kore module text | `params-NAME.json` optional (e.g. `name-as-id`) |
| `state-NAME.send` | sent verbatim as a full JSON-RPC envelope | — |
| `response-NAME.json` | expected full JSON-RPC response | `id` must be `1` |

See `booster/test/rpc-integration/README.md` for `runDirectoryTest.sh` usage and how to
pretty-print Kore terms from request/response files.
