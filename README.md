# The Kore Language

Kore is the "core" part of the K framework.

## What is Kore all about?

In short, we need a formal semantics of K.
In K, users can define formal syntax and semantics of
programming languages as K definitions, and automatically obtain
parsers, interpreters, compilers, and various verification tools
for their languages.
Therefore K is a language-independent framework.

Thanks to years of research in matching logic and reachability
logic, we know that all K does can be nicely formalized as
logic reasoning in matching logic.
To give K a formal semantics, we only need to formally specify
the underlying matching logic theories with which K does reasoning.
In practice, these underlying theories are complex and often
infinite, and it is tricky to specify infinite theories without
a carefully designed formal specification language.
And Kore is such a language.

## Structure of this project

The `/docs` directory contains a comprehensive document _Semantics of K_
that describes the mathematical foundation of Kore, and a BNF grammar
that defines the syntax of Kore language.

The `kore` project is an implementation in Haskell of a Kore parser and symbolic execution engine,
for use with the [K Framework] as a backend.

## Building

Besides [git], you will need [stack] or [cabal] to build `kore`.

```sh
stack build kore
# or
cabal build kore
```

If using `cabal`, version 3.0 or later is recommended.

## Developing

Developers will require all the dependencies listed above.
We also recommend (but not require!) the following dependencies.

For setting up a development environment, we recommend:

- [direnv] to make the project's tools available in shells and editors.
- [ghcide], an integrated development environment for Haskell
  that is compatible with most editors. Note: [yq] is required to
  run `ghcide` with `hie-bios.sh`.
- [hlint] and [stylish-haskell] for compliance with project guidelines. Run
  `stack --stack-yaml global-stack.yaml install hlint stylish-haskell` to
  install the versions that are used for CI.

For integration testing, we also recommend:

- GNU [make]
- The [K Framework] frontend, or [curl] to fetch an appropriate version.
  The frontend has other dependencies, most notably a Java runtime.

### Developing with Nix

For developers so inclined, we provide a `shell.nix` expression with a suitable
development environment and a binary cache at [kore.cachix.org]. The development
environment is intended to be used with `nix-shell` and `stack --no-nix
--system-ghc`.


[git]: https://git-scm.com/
[stack]: https://www.haskellstack.org/
[cabal]: https://haskell.org/cabal
[K Framework]: https://github.com/kframework/k
[curl]: https://curl.haxx.se/
[make]: https://www.gnu.org/software/make/
[direnv]: https://github.com/direnv/direnv
[ghcide]: https://github.com/digital-asset/ghcide
[yq]: https://github.com/kislyuk/yq
[hlint]: https://github.com/ndmitchell/hlint
[stylish-haskell]: https://github.com/jaspervdj/stylish-haskell
[kore.cachix.org]: https://kore.cachix.org/
