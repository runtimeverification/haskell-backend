# Per-request log capture (`haskell-logging`)

Exercises the `haskell-logging` JSON-RPC request flag and the corresponding
`haskell-log-entries` response field. The request carries a **list of
entry/context names** to capture; the matching log entries are returned in-band.

`test.sh` sends `execute` requests against the small `a-to-f` definition
(reused via the `resources/haskell-log-capture.kore` symlink) and asserts:

1. a list of booster context names (`params-contexts.json`) yields a non-empty
   `haskell-log-entries` array;
2. narrowing the list to just `["Proxy"]` (`params-proxy-only.json`) still
   captures entries, and *every* captured entry carries a proxy context — i.e.
   the list selects per request;
3. omitting the flag (`params-control.json`) omits `haskell-log-entries`.

Names route across both engines: kore entry-type names (e.g.
`DebugAttemptEquation`) are resolved against the kore log registry, booster
context names (e.g. `Proxy`, `Rewrite`) against the message context stack
(tag-only for id-carrying contexts like `CtxRewrite`); a name unknown to both is
skipped. The capture happens in the proxy, so the test runs only under
`kore-rpc-booster`. Entries are not diffed against a golden file because their
content is timing-sensitive; the test asserts on presence/selection.
