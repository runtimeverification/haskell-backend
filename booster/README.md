# Haskell Backend Booster

A simpler and faster version of [K-Framework's haskell-backend](../haskell-backend).

* A simple rewrite engine that focuses on the K configuration as the main term
* Aims to solve _easy and common_ rewrites quickly, rather than _all_ rewrites completely
* Reverts to the standard backend for complex unification and term simplification

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

If you want to open a shell for a different version of ghc (currently supporting `ghc924` and `ghc8107`), use

```bash
nix develop .#ghc924
```
or

```bash
nix-shell --argstr ghc ghc924
```

#### Nix-direnv

Using a version of direnv that works with nix (https://github.com/nix-community/nix-direnv) allows seamless loading and unloading of the nix shell, which adds all the required packages such as `cabal`, `hpack`, `fourmolu`, etc. Use the above link to install `nix-direnv`, making sure to hook direnv into whichever shell you are using (https://direnv.net/docs/hook.html). You can use the default nix shell (currently GHC version 9.2.5) by running

```bash
echo "use nix" > .envrc
```

If you want to use a different version of GHC for your shell, e.g. `ghc924`, use

```bash
echo "use flake .#ghc924" > .envrc
```

Finally, run `direnv allow` inside the repo folder to load up the nix shell.

Note that only `cabal` currently works within the nix shell and since it does not support the HPack `package.yaml` file format, any changes to this file will require running `hpack` before they are picked up by cabal.

### HLS in VSCode

To get HLS working in VSCode, install these two extensions:

https://marketplace.visualstudio.com/items?itemName=arrterian.nix-env-selector
https://marketplace.visualstudio.com/items?itemName=haskell.haskell

The `nix-env-selector` extension may prompt for the workspace to be re-loaded. Once re-loaded, HLS should start working. In case you need to use a specific version of ghc for this extension, modify the `.vscode/settings.json` file here:

```json
  "nixEnvSelector.args": "--argstr ghc ghc924"
```