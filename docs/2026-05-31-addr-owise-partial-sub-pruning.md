# Reproduction request: `#addr [owise]` indeterminate-sibling handoff

**To:** pyk team (relay to KEVM downstream as needed).
**From:** haskell-backend / booster team.
**Date:** 2026-05-31.
**In response to:** your `booster-matcher-gaps-gasexec-addr-handoff.md` (2026-05-31).

## What we're building

We're implementing a targeted fix in booster for **case 2** of your handoff (the `#addr [OP:OpCode]` case where `[owise]` is blocked by an indeterminate higher-priority sibling).

We are **not** taking case 1 (`#gasExec(SSTORE)` / `<substate>`-as-variable) on the booster side — that one we're pushing back as a semantics-side fix; you can close those handoffs as expected Kore fallbacks once the auto-abstraction change lands.

The fix for case 2 is narrower than the case-split generalisation you proposed and doesn't have the soundness concern:

> When `MatchIndeterminate` is reached, the matcher has already accumulated a partial substitution from the pairs it *did* resolve.
> Before aborting, we apply that partial substitution to the rule's `requires` clause and run the equation simplifier.
> If any clause simplifies to a concrete `false`, the rule cannot fire under any extension of the match, so we skip it (`returnNotApplied`) instead of aborting.
> If the simplifier can't conclude, we abort exactly as today.

For `#addr [PUSH 1]` against a symbolic wordStack:
the `<k>` cell match binds `OP ↦ PUSH 1` into the partial substitution before the indeterminate `<wordStack>` pair is hit; `isAddr2Op(PUSH 1)` then evaluates concretely to `false`; the Addr2Op rule is skipped; the catch-all fires.
No Kore handoff.

We want to land this with both an algorithm-level unit test (which we'll write against a synthetic K definition) **and** a regression test built from your actual failing case.
This document is asking for the latter.

## What we need from you

The cleanest deliverable is a **bug-report tarball** produced by `kore-rpc-booster`'s built-in `--bug-report` flag, capturing the request that aborts to Kore on the `#addr` handoff.

Our existing tooling (`scripts/tarball-to-rpc-test.sh`) converts such tarballs directly into `runDirectoryTest`-compatible regression tests under `booster/test/rpc-integration/`, with the `.kore` definition, the LLVM backend definition, and the exact request/response pairs all bundled.
No K source, no K toolchain, no version pinning required on our side to replay.

The full workflow is documented in `haskell-backend/docs/2026-05-25-submitting-test-cases.md`; the relevant short version:

```sh
kore-rpc-booster definition.kore \
    --main-module <MODULE> \
    --llvm-backend-library <interpreter.so> \
    --bug-report addr-owise-handoff \
    [other flags as in the recover-mode sweep run]
```

Trigger the `#addr` handoff exactly as the recover-mode sweep does (the spec from `evm-semantics/docs/experiment-logs/2026-05-31T164118Z-recover-mode-sweep-post-fix.md`), then shut the server down.
That produces `addr-owise-handoff.tar.gz`.

## What we'd like included (or noted) alongside the tarball

The tarball itself is self-contained for replay, but a few pieces of context make the regression assertions much sharper:

1. **The spec and request id**: which spec from the post-fix sweep, and the `request_id` of the `#addr` kore-execute handoff inside that spec's `recover-logs/`.
   (We just need to know which RPC call in the tarball is the `#addr` handoff — it'll be one of several requests in sequence.)

2. **Today's response for that request** (you'll already have it in your recover-log).
   We want to assert against the *new* expected response (rule fires, no `aborted` reason), not just "doesn't crash."

3. **The K source for the three `#addr` rules** as quoted in your handoff (`evm.md:519`, `523`, `527`), plus the `isAddr1Op` / `isAddr2Op` simplification equations.
   Not strictly required for the integration test — the `.kore` definition in the tarball has the lowered form — but it makes the test directory's `README.md` actually readable.

4. **The expected post-fix outcome from KEVM's perspective**: i.e. "after this fix lands, this proof should complete without Kore-execute handoffs on `#addr`" (or with N fewer handoffs).
   Just one sentence, so the regression test asserts the right thing.

## What we don't need

- Don't strip the tarball or hand-edit it; the tooling assumes the standard layout.
- Don't bundle `recover-logs/*.jsonl` files — they're useful for diagnosing aborts but not for the regression test itself (the tarball already has the request/response).
- Don't try to isolate the K dependency for us; the tarball doesn't need K. Send the whole `.kore` definition as captured.

## If a bug-report tarball isn't easy to produce

A second-best path: send us
(a) the `definition.kore`, `interpreter.so` (LLVM library), and `request_id` for the `#addr` handoff;
(b) the request JSON (`recover-logs/{request_id}.jsonl` has the request body in the `params` field);
(c) the current (aborting) response JSON.

We can stitch these into a tarball-equivalent on our side.

If even *that* is hard — e.g. the LLVM library has a crypto-plugin dependency you can't easily ship — let us know what the blocker is.
We have a fallback (`PLUGIN_DIR`-based on-the-fly rebuild, documented in `2026-05-25-submitting-test-cases.md`), but it's worth knowing upfront.

## Verification we'll do once we have it

1. Replay the tarball against the current booster — confirm we reproduce the `aborted` response (with `reason: "aborted"` and `RuleApplicationUnclear` in the trace).
2. Build with the fix applied — confirm the response no longer aborts and that the catch-all `#addr` rule label appears in the rewrite trace.
3. Convert to an `rpc-integration` test directory; the test passes the golden response against the fixed booster.

Once those three steps are green we'll land the fix with the regression test in the same PR.

## Where to send

Drop the tarball (and any short answer to the four context questions above) in whichever channel we've been using.
If it's too large for chat, a link to a shared drive / S3 / artifact bucket works.
A GitHub issue on `runtimeverification/haskell-backend` referencing this document and attaching the tarball is also fine.

Thanks — this will let us pin the user-facing regression cleanly rather than just synthetic coverage.
