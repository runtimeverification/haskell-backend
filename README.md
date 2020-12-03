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

Developers will require all the dependencies listed above,
in addition to the requirements and recommendations below.

### Required dependencies

For packaging, we require:

- [Nix], a tool for reproducible builds and deployments.

Refer to instructions at [kore.cachix.org] to set up the binary cache.
Refer to the section [below](#developing-with-nix) for more instructions,
and to learn why this is required.

For integration testing, we require:

- GNU [make]
- The [K Framework] frontend, or [curl] to fetch an appropriate version.
  The frontend has other dependencies, most notably a Java runtime.

### Recommended dependencies

For setting up a development environment, we recommend:

- [direnv] to make the project's tools available in shells and editors.
- [ghcide] or [haskell-language-server], [language servers] for Haskell that are
  compatible with most editors. See instructions
  [below](#running-a-language-server) to run a language server.
- [hlint] and [stylish-haskell] for compliance with project guidelines.

### Running a language server

To run a language server, developers will need to activate the appropriate
`hie.yaml` file:

```sh
ln -s hie-stack.yaml hie.yaml  # for Stack
# or
ln -s hie-cabal.yaml hie.yaml  # for Cabal
# or
ln -s hie-bios.yaml hie.yaml  # if all else fails
```

The project's dependencies must be installed before starting the language
server:

```sh
stack build --test --bench --only-dependencies
# or
cabal build --enable-tests --enable-benchmarks --only-dependencies kore
```

### Developing with Nix

We provide a `shell.nix` expression with a suitable development environment and
a binary cache at [kore.cachix.org]. The development environment is intended to
be used with `nix-shell` and `cabal`.

When the `.cabal` package description file changes, run:

```.sh
# Requires Nix to be installed.
./nix/rematerialize.sh
```


[git]: https://git-scm.com/
[stack]: https://www.haskellstack.org/
[cabal]: https://haskell.org/cabal
[K Framework]: https://github.com/kframework/k
[curl]: https://curl.haxx.se/
[make]: https://www.gnu.org/software/make/
[direnv]: https://github.com/direnv/direnv
[ghcide]: https://github.com/digital-asset/ghcide
[haskell-language-server]: https://github.com/haskell/haskell-language-server
[language servers]: https://langserver.org/
[hlint]: https://github.com/ndmitchell/hlint
[stylish-haskell]: https://github.com/jaspervdj/stylish-haskell
[kore.cachix.org]: https://kore.cachix.org/
[Nix]: https://nixos.org
