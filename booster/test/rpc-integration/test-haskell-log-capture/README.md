# Per-request log capture (`haskell-logging`)

Exercises the `haskell-logging` JSON-RPC request flag and the corresponding
`haskell-log-entries` response field.

`test.sh` sends two `execute` requests against the small `a-to-f` definition
(reused via the `resources/haskell-log-capture.kore` symlink):

- one with `haskell-logging: true`, asserting the response carries a non-empty
  `haskell-log-entries` array;
- one without the flag, asserting the field is omitted entirely.

The capture-and-attach happens in the proxy (`booster/tools/booster/Proxy.hs`),
so the test only runs under `kore-rpc-booster`. The entries themselves are not
diffed against a golden file because their content is timing- and
scheduling-sensitive; the test asserts on presence/absence and non-emptiness.
