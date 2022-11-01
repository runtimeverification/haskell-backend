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

* Prerequisites: `stack` or `cabal`, `ghc-9.2.4`
* Stackage resolver: `nightly-2022-10-31` (`ghc-9.2.4`)
