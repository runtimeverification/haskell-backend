# Logging Kore Backend Invocations — Input/Output Capture Guide

This document is aimed at downstream agents and tooling that need to observe **every
invocation of the old Kore backend** inside `kore-rpc-booster`, capture the term
before and after, and determine whether Kore contributed anything. It covers all
three RPC endpoints (simplify, execute, implies) and is tuned for **minimum
additional overhead** beyond what is strictly required to answer the question.

---

## Architecture recap

`kore-rpc-booster` runs two engines in one process. The proxy
(`booster/tools/booster/Proxy.hs`) routes each RPC call:

| Endpoint | When Kore is called |
|----------|---------------------|
| `simplify` | **Always** — Booster runs first, its output is passed to Kore unconditionally (`handleSimplify`, lines 171–214). |
| `execute` | **On fallback only** — when Booster stops with a reason in `fallbackReasons` (default: `Aborted`, `Stuck`, `Branching`). Kore executes one step. |
| `implies` | **Conditionally** — only when `assumeDefined = true` in the request and Booster's implies endpoint fails. Otherwise Kore handles the whole call. |
| `get-model` | Kore re-checks only when Booster returns `Unknown`. |
| `add-module` | Kore always runs (response is empty, overhead is negligible). |

---

## What "input/output" means per endpoint

### `simplify`

- **Input to Kore**: `boosterRes.state` — whatever Booster returned.
  This is the JSON-RPC `state` field of the `SimplifyRequest` sent to Kore
  (`Proxy.hs:179`): `Simplify simplifyReq { state = boosterRes.state }`.
- **Output from Kore**: `koreRes.state` in the `SimplifyResult`.
- **Kore changed anything?**: `koreRes.state /= boosterRes.state`.
  The proxy already checks this and logs a diff when it differs (see Signal 1 below).

### `execute` (fallback)

- **Input to Kore**: `execStateToKoreJson simplifiedBoosterState` — Booster's
  halted state, optionally after a pre-fallback simplification pass
  (`Proxy.hs:354–358`). The request has `maxDepth = Just (Depth 1)`.
- **Output from Kore**: `koreResult.state` plus `koreResult.reason` (the halt reason
  after that one step).
- **Kore changed anything?**: `koreResult.depth > 0` (Kore made at least one step)
  and/or `koreResult.reason /= boosterResult.reason`.

### `implies`

- **Input to Kore**: the original `ImpliesRequest` verbatim (Booster's result was
  discarded after failure, `Proxy.hs:117`).
- **Output from Kore**: `koreRes` from the implies endpoint.
- **Kore changed anything?**: any non-error result from Kore counts as contribution.

---

## The two existing zero-overhead signals

Before adding any new logging, check these two signals — they require no code changes
and have near-zero runtime cost:

### Signal 1: structural diff (`-l Aborts`)

The proxy already emits:
```
[proxy][abort][detail] Kore simplification: Diff (< before - > after)
```
under the `Aborts` log level **only when `koreRes.state /= boosterRes.state`**.
Absence of this line for a given request means Kore returned byte-for-byte
identical output to Booster.

To enable: pass `-l Aborts` (or `--log-level Aborts`) to `kore-rpc-booster`.
Format: JSON (`--log-format json`) or plain text.
Overhead: negligible — the diff is only computed and printed when there IS a change.

### Signal 2: equation attempts (`-l SimplifyKore -l Timing`)

`DebugAttemptEquation` entries from Kore's internal logger fire on every equation
Kore tries to apply. If none appear, Kore hit the `isSimplified` early-exits in its
fixpoint loop and evaluated nothing.

To enable: `-l SimplifyKore -l Timing` (the `-l Timing` is required to set
`contextLoggingEnabled = True`, without which the kore-side log entries are suppressed
— see `Server.hs:156`).

Overhead: moderate when equations ARE being attempted (one log line per attempt).
Near-zero when Kore does nothing (no entries emitted).

---

## Capturing full input/output terms with minimum overhead

The signals above tell you *whether* Kore contributed; the following tells you *what*
it contributed. Capturing full terms is inherently more expensive than logging metadata.
Choose the lowest level that answers your question.

### Level 0 — metadata only (cheapest)

Run with `-l Aborts -l Timing`. Parse the structured log:

- `[proxy][timing]` lines give per-request timing broken down by `koreTime` vs total.
  `koreTime > 0` confirms Kore was invoked and how long it spent.
- `[proxy][abort]` lines with `Kore simplification: Diff` confirm Kore changed state.
- For execute fallbacks: `[proxy][abort]` lines like
  `"Booster Aborted at depth N"` and `"kore depth-bound, continuing..."` show
  when and how many fallback steps Kore took.

Parse target: the `[proxy]` context in Booster's log format:
```
[request <id>][booster][proxy][abort] Booster Stuck at depth 42
[request <id>][booster][proxy][timing] Performed ExecuteM in 1.23s (0.45s kore time)
```

### Level 1 — Kore's input only (low overhead when Kore rarely fires)

The proxy sends the Booster-simplified state to Kore as a JSON-RPC request.
Intercept it with a **request-logging middleware** or by enabling JSON-format logging
and filtering for Kore-bound messages. The input term is already present in the
request object.

Alternatively: add a log statement in `Proxy.hs:handleSimplify` immediately before
the `kore koreReq` call:
```haskell
Booster.Log.withContext CtxProxy $
    Booster.Log.logMessage $
        "Kore simplify input: " <> toStrict (encodeToLazyText boosterRes.state)
```
This fires once per simplify request. For the execute fallback, the analogous point
is immediately before the `kore (Execute r{...})` call at `Proxy.hs:353`.

Cost: O(N) JSON serialization of the input term, once per Kore invocation.

### Level 2 — Kore's input AND output, diff computed by caller (recommended)

Log both `boosterRes.state` (input to Kore) and `koreRes.state` (Kore's output) as
JSON at the proxy level. The downstream tool receives two KoreJson terms and can diff
them however it likes.

**Recommended log point** — add to `Proxy.hs:handleSimplify` around line 186,
replacing the existing diff-only log with a structured log that always emits
input + output when called (or only when they differ — your choice):

```haskell
-- After receiving koreResult (line ~183):
Booster.Log.withContext CtxProxy $
    Booster.Log.withContext CtxDetail $
        Booster.Log.logMessage $
            "kore-simplify"
                <> " input=" <> toStrict (encodeToLazyText boosterRes.state)
                <> " output=" <> toStrict (encodeToLazyText koreRes.state)
```

For execute fallbacks, log around `Proxy.hs:353–373`:
```haskell
Booster.Log.withContext CtxProxy $
    Booster.Log.withContext CtxDetail $
        Booster.Log.logMessage $
            "kore-execute-fallback"
                <> " input=" <> toStrict (encodeToLazyText (execStateToKoreJson simplifiedBoosterState))
                <> " output=" <> toStrict (encodeToLazyText (execStateToKoreJson koreResult.state))
                <> " reason=" <> Text.pack (show koreResult.reason)
```

Downstream agents parse lines containing `"kore-simplify"` or `"kore-execute-fallback"`,
extract the `input=` and `output=` JSON blobs, and diff them.

Cost: O(N) JSON serialization per Kore invocation. If Kore is invoked rarely (execute
fallback) this is negligible; for simplify (always invoked) it is one serialization
per request which may be significant for large terms.

**Conditional variant** — emit only when terms differ (add an `unless` guard):
```haskell
unless (koreRes.state == boosterRes.state) $ Booster.Log.withContext CtxProxy $ ...
```
This makes the log line zero-cost when Kore does nothing, at the expense of not
capturing the no-op cases.

### Level 3 — full Kore internal trace (highest overhead, for debugging only)

`-l SimplifyKore` + `-l RewriteKore` + `-l Timing` enables Kore's internal
`DebugAttemptEquation`, `DebugAppliedRewriteRules`, and `DebugTerm` entries.
This produces one log entry per equation attempt with the full term.
**10–14× slowdown** (measured). Use only on targeted small inputs.

---

## Recommended minimal setup for downstream analysis

```
kore-rpc-booster \
    <definition args> \
    --log-file run.jsonl \
    --log-format json \
    -l Aborts \
    -l Timing
```

Then apply **Level 2** patches to `Proxy.hs` (emit input+output as JSON on every
Kore invocation, unconditionally).

Post-processing pipeline:
1. Filter `run.jsonl` for lines with `"kore-simplify"` or `"kore-execute-fallback"`.
2. For each such line, extract `input` and `output` KoreJson blobs.
3. Run your term-diff tool on the pair.
4. Count: total invocations, changed invocations, and size of the delta.

The `count-aborts` tool in `dev-tools/` provides a starting point for aggregating
abort statistics from JSON logs; its source is a useful reference for log parsing.

---

## What the log lines look like per endpoint

### `simplify` — Kore invoked, no change

```json
{"context":["request 1","booster","proxy"],"message":"Simplifying booster state and falling back to Kore"}
{"context":["request 1","booster","proxy","detail"],"message":"kore-simplify input=<koreJson> output=<koreJson>"}
{"context":["request 1","booster","proxy","timing"],"message":{"method":"SimplifyM","time":2.1,"koreTime":1.8}}
```

### `execute` — fallback step taken

```json
{"context":["request 2","booster","proxy","abort"],"message":"Booster Aborted at depth 5"}
{"context":["request 2","booster","proxy"],"message":"Executing fall-back request"}
{"context":["request 2","booster","proxy","detail"],"message":"kore-execute-fallback input=<koreJson> output=<koreJson> reason=DepthBound"}
{"context":["request 2","booster","proxy","timing","kore"],"message":{"method":"ExecuteM","time":0.3,"koreTime":0.3}}
```

### `implies` — Booster failed, Kore took over

```json
{"context":["request 3","booster","proxy","abort"],"message":"Implies abort in booster: <reason>. Falling back to kore."}
```
(No term logging here by default — Kore receives the original request verbatim.)

---

## Source locations for patch targets

All paths relative to `haskell-backend/`.

| What to patch | File | Approximate line |
|---------------|------|-----------------|
| `handleSimplify` — after kore returns | `booster/tools/booster/Proxy.hs` | 183–212 |
| Execute fallback — before kore call | `booster/tools/booster/Proxy.hs` | 350–360 |
| Execute fallback — after kore returns | `booster/tools/booster/Proxy.hs` | 373–456 |
| Implies fallback | `booster/tools/booster/Proxy.hs` | 113–119 |
| `CtxDetail` context definition | `booster/library/Booster/Log.hs` | (search `CtxDetail`) |
| Booster log message type | `booster/library/Booster/Log.hs` | `logMessage` |
