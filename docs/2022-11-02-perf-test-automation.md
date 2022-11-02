# Performance Test Automation in the Repository

Two different github actions are in place for performance related work

1. Time-limited profiling runs using uploaded tar-balls
2. Timed KEVM proof suite runs, comparing to master (for pull requests only)

Both actions are triggered using comments that contain a particular string.
Only members of the RV organization are allowed to trigger the actions, and the trigger only works for issues or pull requests (PRs) with label `(performance)`.

A message with a link to the action is posted as a comment.  
Upon completion, a second message indicating success or failure is posted as a comment.

Actions are implemented as nix derivations, i.e. they run in their own isolated environment, possibly using particular versions of their dependencies.

## 1. Profiling runs

[github action](../.github/workflows/profiling.yaml), 
[run-profiling.nix](../nix/run-profiling.nix)

### Trigger Event
- a comment containing the string `".tar.gz)"` (anywhere)
- written or edited by a member of the RV organization
- on an issue or PR with label `(performance)`

It is assumed that this string is part of a _link to a github file attachment in the Haskell backend repository, with suffix `.tar.gz`_ which was created using the `--bug-report` option of the Haskell backend. Such tarballs contain the required data and a shell script to reproduce a particular invocation of `kore-exec`.

### Action

The action will extract the (assumed) markdown link URL from the comment.
After checking the preconditions (organization membership, attachment file downloadable under given URL), the tarball will be extracted and used for several runs:

1. a normal `kore-exec` run with event logging switched on.  
   **Output:** event-log`kore-prof.eventlog`.  
   The output can be used to analyze execution at a high level, directly or with speedscope after converting it with the `kore-prof` tool.
2. a run with profiling (with a profiling-enabled, GHC-9 built, `kore-exec`).  
   **Output:** 
   - textual profiling data `kore-exec.prof`, to view directly
   - `prof-speedscope.json` created from profiling event log with `hs-speedscope`, to view in [Speedscope](https://speedscope.app).
3. a run with heap profiling (GHC-9 build with profiling)  
   **Output:** heap graph `heap-cost-centers.[svg|html]`, to view directly and in browser
4. a run with info-table profiling (GHC-9 specific)
   **Output:** `heap-infotables.html`, to view in a browser

All runs are time-limited to 4 minutes by default (the timeout is adjustable in the nix invocation but not in the trigger event).

The artifacts have considerable size (even when compressed into a tarball).

## 2. Timings for KEVM proofs

[github action](../.github/workflows/kevm-performance-test.yaml) (here), 
[profile.nix](https://github.com/runtimeverification/evm-semantics/blob/master/package/nix/profile.nix)
[flake.nix](https://github.com/runtimeverification/evm-semantics/blob/master/flake.nix)
(in evm-semantics repository)

### Trigger event
- a comment containing the string `"/KEVM-perf-run"`(anywhere)
- written or edited by a member of the RV organization
- on a PR (not an issue) with label `(performance)`

Optionally, the trigger string can be followed by a single space and a version tag (matching regex `v[0-9]+(\.[0-9]+){2}`). This tag is used to determine the K version for the test. If no such tag is given, `master` will be used.

### Action

All KEVM proofs will be run, measuring the time they individually take, using the method described in [evm-semantics issue 1165](https://github.com/runtimeverification/evm-semantics/issues/1165).
This is done _twice_, once using the head commit of the PR that was commented on to supply `kore-exec`, and once with the commit the PR is based upon. The K framework version will be `master` unless a tag was given in the trigger comment.

After both runs (which may take >2h), a script is run that produces a timing comparison table.

Both timing data files and the comparison table are stored as artifacts. the following 3 files should be stored:
- `KEVM-timing-${TIMESTAMP}-${PR_HEAD}.data` (timing data with code from PR)
- `KEVM-timing-${TIMESTAMP}-master.data` (timing data with code from HS backend master/base commit)
- `KEVM-timing-comparison.data` (comparison table in gfm format)
