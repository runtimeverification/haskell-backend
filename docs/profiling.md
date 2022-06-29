# Profiling and debugging

There are two main ways we may want to profile the Haskell binaries in this repo. One is to do with how much time our program is spending on various stages of execution and the other is to do with how much memory it uses to do so. The first question may help us answer how to make our algorithms more efficient, whilst the second is more to do with Haskell's laziness, which often results in memory leaks. However, analyzing the memory usage can be beneficial not just for detecting memory leaks, but may point to inefficiencies such as preforming unnecessary re-computations, etc.


In order to perform most of the profiling mentioned in this document, all the profiled binaries have to be compiled with profiling enabled. There are several options to do this via Cabal, Stack or Nix

## Compile options

There are two main options we have to set when profiling. Firstly we have to pass cabal/stack a `profiling: True` / `--profiling` flag, which builds the `kore` library and all it's dependencies with profiling information (passes the `-prof` flag to GHC). We can also pass profiling detail options corresponding to GHCs `-fprof-auto`/`-fprof-auto-top`/`-fprof-auto-exported` options [documented here](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/profiling.html), which insert `SCC` (Set Cost Centre) annotations, used for the time and (some) memory based profiles. Other flags for specific profiling options, found in the tables below, should be passed in via `ghc-options` to the compiler.

### Cabal

Profiling options for Cabal can be set via the `cabal.project`/`cabal.project.local` file. The relevant options that need to be added are:

```
package *
  profiling: True
```

to enable profiling in all packages including the libraries, as well as adding a [`profiling-detail`](https://cabal.readthedocs.io/en/3.4/cabal-project.html#cfg-flag---profiling-detail) to the `kore` package

```
package kore
  profiling-detail: toplevel-functions
```

*Note: By default, cabal applies `exported-functions` for libraries and `toplevel-functions` for executables.*


### Stack

This command will build `kore` with profiling enabled:

```
stack --profile build
```

we can then run individual binaries with supplied RTS runtime options using

```
stack --profile exec -- kore-exec +RTS <profiling_flags_here>
```

*Note: Stack doesn't seem to have as much level of control over profiling options as cabal, e.g. there doesn't seem to be a way of setting the `profiling-detail` in the same way Cabal does, see https://github.com/hasura/graphql-engine/issues/3280 and https://github.com/commercialhaskell/stack/issues/2853.*

### Nix (preferred)

With nix flakes, we have a nice convenience `nix shell` command, which builds a flake derivation and adds the bin folder of the result to the `PATH` of our current shell. Our [`flake.nix`](./flake.nix) contains several such expressions for the `kore-exec` binary, which gets compiled with the correct build flags and also gets passed the correct runtime flags for whichever analysis we are currently attempting to perform. Currently, we have the following versions of `kore-exec-prof`:

```
nix shell .#kore-exec-prof
nix shell .#kore-exec-prof-infotable
```

Running any of the commands above will build a profiled version of `kore-exec` using GHC >=9.2.3 with the requisite GHC compile arguments. Once compiled, run `kore-exec` with RTS arguments corresponding to kind of profile you are interested in running (see tables below). Any other useful profiling pre-sets should be added to the flake for ease of use as well as documentation purposes.


## Runtime options

### Time Profiles

| RTS Flag | GHC Compile flag | Description | Output |
|---|---|---|---|
| `-p` | `-prof -fprof-auto`/<br>`-prof -fprof-auto-top`/<br>`-prof -fprof-auto-exported` | Produces a standard time profile report. Can be visualized via [`ghc-prof-flamegraph`](https://github.com/fpco/ghc-prof-flamegraph/), [`profiteur`](https://github.com/jaspervdj/profiteur) or [`profiterole`](https://github.com/ndmitchell/profiterole) | `⟨program⟩.prof` |
| `-p` | `-prof -fprof-callers=⟨name⟩` | Automatically enclose all occurrences of the named function in an `SCC`. Note that these cost-centres are added late in compilation (after simplification) and consequently the names may be slightly different than they appear in the source program. |  |
| `-l` | `-prof -eventlog`<br>(corresponds to `.#kore-exec-prof`) | Log events in binary format. This logs a default set of events, use [`hs-speedscope`](https://github.com/mpickering/hs-speedscope) with [`speedscope`](https://www.speedscope.app/) to view. | `⟨program⟩.eventlog` |
| `-l-au` | `-prof -eventlog` | Disable all log event classes except for user events. These are events emitted from Haskell code using functions such as <br>`Debug.Trace.traceEvent`. For other options, see https://ghc.gitlab.haskell.org/ghc/doc/users_guide/runtime_control.html#rts-eventlog | `⟨program⟩.eventlog` |
| `-l` / `-l-aus` |  | Log only kore related events. This logging can be performed on `kore-exec` even without `-profiling` enabled during compilation and uses the `traceProf` function (defined via [`traceEventIO`](https://hackage.haskell.org/package/base/docs/Debug-Trace.html#v:traceEventIO)). To view the events, `kore-prof` must be used along with [`speedscope`](https://www.speedscope.app/). | `⟨program⟩.eventlog` |


### Heap profiles

The table below lists compile and runtime options in (roughly) increasing level of granularity. See the [RTS options for heap profiling](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/profiling.html#rts-options-heap-prof) section of the GHCdocs for further details.

| RTS Flag | GHC Compile flag | Description | Output |
|---|---|---|---|
| `-hT` |  | Generates a basic heap profile, in the file. Breaks down the graph by heap [closure type](https://hackage.haskell.org/package/ghc-heap-9.0.1/docs/GHC-Exts-Heap-ClosureTypes.html). To produce the heap profile graph, use [`hp2ps`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/profiling.html#hp2ps) or [`eventlog2html`](https://mpickering.github.io/eventlog2html/).<br>*It seems .hp profiles are being phased out and you should probably just use the eventlog based heap profiling instead.* | `⟨program⟩.hp` |
| `-l -hT` | `-prof -eventlog` | Breaks down the graph by [closure type](https://hackage.haskell.org/package/ghc-heap-9.0.1/docs/GHC-Exts-Heap-ClosureTypes.html). Use [`eventlog2html`](https://mpickering.github.io/eventlog2html/) to visualize. | `⟨program⟩.eventlog` |
| `-l -hy` | `-prof -eventlog`<br>(corresponds to `.#kore-exec-prof`) | Breaks down the graph by (approximate) type (e.g. `Int`, `Maybe String`, `(->)`). | `⟨program⟩.eventlog` |
| `-l -hd` | `-prof -eventlog` | Breaks down the graph by closure description (e.g. `Just`, `THUNK`). | `⟨program⟩.eventlog` |
| `-l -hc` | `-prof -eventlog` | Breaks down the graph by lexical scope (known as "cost-centres"). | `⟨program⟩.eventlog` |
| `-l -hi` | `-prof -eventlog -fdistinct-constructor-tables -finfo-table-map` <br>(corresponds to `.#kore-exec-prof-infotable`) | `-hi` collates heap allocations by their info table identity<br/>`-fdistinct-constructor-tables` tells the code generator to produce a distinct info table for each constructor allocation (new in GHC 9.2)<br/>`-finfo-table-map` tells the code generator to produce an auxiliary data structure which allows distinct info tables to be mapped back to source locations | `⟨program⟩.eventlog` |

### Debugging

The profiling information can also be useful when hunting for other bugs, such as runtime exceptions, which can be difficult to find, since Haskell does not print a stack trace (by default) when such an exception occurs.

| RTS Flag | GHC Compile flag | Description | Output |
|---|---|---|---|
| `-xc` | `-prof -fprof-auto` | Causes the runtime to print out the current cost-centre stack whenever an exception is raised. Useful for debugging the location of exceptions, such as `Prelude.head: empty list` error. | stderr |


## Costs and disadvantages of profiling

There are two main issues with profiling:

1) Profiling adds an overhead to the overall runtime, so it is only useful if we want to measure the relative runtime of different components of our programs
2) The addition of cost centers introduced by `-fprof-auto` (`profiling-detail: all-functions`)/`-fprof-auto-top`/`-fprof-auto-exported` can impede certain optimizations such as fusion, which can skew the profile, since we are now profiling code which would otherwise have been optimized, so the % of time spent in the code region will not reflect the un-profiled runtime. There is a potential workaround to this issue in [GHC 9.2](https://discourse.haskell.org/t/profiling-using-late-cost-centres-after-optimization/4664) with a new [`-fprof-late-ccs` flag in GHC 9.4.1](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/profiling.html) which inserts top-level const centers at a late stage of the optimization pipeline


## Additional resources

* Tutorial on debugging memory usage from Zurihac 2021
  Video: https://www.youtube.com/watch?v=6Ljv5FHGXDM&list=PLiU7KJ5_df6YhHefoPfUP1VSd1AbOC02R&index=2
  Github repo containing written up summary: https://github.com/well-typed/memory-usage-zurihac-2021

* [A First Look at Info Table Profiling](https://well-typed.com/blog/2021/01/first-look-at-hi-profiling-mode/) - an intro to the new `-hi` profiling mode in GHC 9.2
* [Memory Fragmentation: A Deeper Look With ghc-debug](https://well-typed.com/blog/2021/01/fragmentation-deeper-look/) - a demo of the `ghc-debug` tool
* [Ticky-ticky profiling](https://gitlab.haskell.org/ghc/ghc/-/wikis/debugging/ticky-ticky) - low level cost center like profiling which doesn’t interfere with core optimizations, but is not a stable feature. The [`-fprof-late-ccs` flag in GHC 9.4.1](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/profiling.html) seems like a proper alternative.
* [DWARF support in GHC](https://well-typed.com/blog/2020/04/dwarf-1/) and [Towards system profiler support for GHC](https://well-typed.com/blog/2021/07/ghc-sp-profiling/) discuss the possibility of using native profiling tools like Linux's `perf` to get meaningful data on Haskell programs. The second article discusses the possibility of recording Haskell call stacks via `perf`, but this is currently not possible and unlikely in the near future
* [The Layout of Heap Objects](https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects) - potentially useful information when interacting with `ghc_debug`