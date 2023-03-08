# Haskell Backend Booster

A simpler and faster version of [K-Framework's haskell-backend](../haskell-backend).

* A simple rewrite engine that focuses on the K configuration as the main term
* Aims to solve _easy and common_ rewrites quickly, rather than _all_ rewrites completely
* Reverts to the standard backend for complex unification and term simplification

## Kompiling a K definition and running the RPC server

The `hs-backend-booster` binary takes a `kore` file definition, parses and internalises it and then launches an RPC server, which executes requests agains this definition. It additionally accepts a path to a dynamic library compiled by the LLVM backend, which is used for simplification of bool sorted terms. In order to build the kore definition and the shared library out of a K definition, first call

```
kompile --llvm-kompile-type c my_defintion.k
```

and then launch the server via

```
hs-backend-booster ./my_defintion-kompiled/definition.kore --module MY-DEFINITION --llvm-backend-library ./my_defintion-kompiled/interpreter
```


## Development

### Package structure

At the moment, all code lives in a single package. This might change in the future as the software grows in terms of features.

### Building

The software can be built with `stack` or `cabal`.

```sh
$ stack build
  # or
$ cabal build
```

* Prerequisites: `stack` or `cabal`, `ghc-9.2.5`
* Stackage resolver: `nightly-2022-11-17` (`ghc-9.2.5`)

### Nix

There are several things you can do, to make the development via nix as seamless as possible.


#### Nix shell

To open the nix shell you will need nix version 2.4 or newer. Then use either `nix develop` (if you have flakes enabled) or use the old style `nix-shell` command.

If you want to open a shell for a different version of ghc (currently supporting `ghc925` and `ghc8107`), use

```bash
nix develop .#ghc925
```
or

```bash
nix-shell --argstr ghc ghc925
```

You can open a dev shell which contains cabal with all the required libraries compiled with profiling via:

```
nix develop .#ghc925-prof
```

#### Nix-direnv

Using a version of direnv that works with nix (https://github.com/nix-community/nix-direnv) allows seamless loading and unloading of the nix shell, which adds all the required packages such as `cabal`, `hpack`, `fourmolu`, etc. Use the above link to install `nix-direnv`, making sure to hook direnv into whichever shell you are using (https://direnv.net/docs/hook.html). You can use the default nix shell (currently GHC version 9.2.5) by running

```bash
echo "use nix" > .envrc
```

If you want to use a different version of GHC for your shell, e.g. `ghc925`, use

```bash
echo "use flake .#ghc925" > .envrc
```

Finally, run `direnv allow` inside the repo folder to load up the nix shell.

Note that only `cabal` currently works within the nix shell and since it does not support the HPack `package.yaml` file format, any changes to this file will require running `hpack` before they are picked up by cabal.

### scripts/update-haskell-backend.sh

To bump the version of the haskell-backend consistently within the project (i.e. in nix, cabal.project and stack.yaml) call

```
nix run .#update-haskell-backend
```

you can optionally pass a commit hash above if you don't want master.

### HLS in VSCode

To get HLS working in VSCode, install these two extensions:

https://marketplace.visualstudio.com/items?itemName=arrterian.nix-env-selector
https://marketplace.visualstudio.com/items?itemName=haskell.haskell

The `nix-env-selector` extension may prompt for the workspace to be re-loaded. Once re-loaded, HLS should start working. In case you need to use a specific version of ghc for this extension, modify the `.vscode/settings.json` file here:

```json
  "nixEnvSelector.args": "--argstr ghc ghc924"
```

## Eventlog tracing

Besides compiling the backend with profiling mode, we can also enable a targeted profiling mode by emitting useful debug events into the eventlog. So far we can emit/trace the following:

* LLVM backend API calls - using `--trace llvm-calls +RTS -l-au` we can collect all the LLVM backend API calls the server performs during execution. Running the obtained eventlog through `eventlog-parser` will produce an `llvm_calls.c` file of the form:

  ```c
  kore_symbol* sym_m5952705877914568462 = kore_symbol_new("LblnotBool'Unds'");
  kore_pattern* pat_m7294887483024610198 = kore_composite_pattern_from_symbol(sym_m5952705877914568462);
  kore_symbol* sym_2859997003983430356 = kore_symbol_new("LblSet'Coln'in");
  kore_pattern* pat_7796859658648783000 = kore_composite_pattern_from_symbol(sym_2859997003983430356);
  kore_symbol* sym_m6495506210664726973 = kore_symbol_new("inj");
  kore_sort* sort_m1174205405547972024 = kore_composite_sort_new("SortId");
  ...
  ```

* Timing information in IO - using `--trace timing +RTS -lsu` we can instrument code with `Trace.timeIO "foo" ...` calls which will measure time spent in `...` and attach the label `foo` to this region in the speedscope profile. `eventlog-parser` will produce a JSON file of these calls viewable in the speedscope app.
