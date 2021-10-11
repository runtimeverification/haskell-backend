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

The [docs] directory contains a collection of documents
that describe the mathematical foundation of Kore and a BNF grammar
that defines the syntax of Kore language. See
[/docs/introduction.md](https://github.com/kframework/kore/blob/master/docs/introduction.md)
for an overview of the components of Kore.

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

Using [make]:

```sh
make all # builds all binaries
```

## Developing

Developers will require all the dependencies listed above,
in addition to the requirements and recommendations below.

### Required dependencies

For integration testing, we require:

- GNU [make]
- The [K Framework] frontend.

Instead of installing the frontend, you can use our `Dockerfile`
to run the integration tests inside a container.
Use `docker.sh` to run commands inside the container:

``` sh
./docker/build.sh  # run once when dependencies change
./docker/run.sh make all  # build the backend
./docker/run.sh make test  # run all tests
./docker/run.sh make -C test/imp test  # run all tests in test/imp
```

### Recommended dependencies

For setting up a development environment, we recommend:

- [direnv] to make the project's tools available in shells and editors.
- [haskell-language-server], a [language server] for Haskell that is compatible
  with most editors. See instructions [below](#running-a-language-server) to run
  a language server.
- [hlint] for compliance with project guidelines.
- [entr] and [fd] for running `./entr.sh` to keep important files up-to-date.

We recommend to keep `./entr.sh` running in the background
to keep important files (such as package descriptions) up-to-date,
especially if the developer is using Cabal.

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

This script is also run by an automatic workflow.

We provide a `test.nix` for running integration tests:

``` sh
nix-build test.nix  # run all integration tests
nix-build test.nix --argstr test imp  # run the integration tests in test/imp
nix-shell test.nix  # enter a shell where we can run tests manually
```

[docs]: https://github.com/kframework/kore/tree/master/docs
[git]: https://git-scm.com/
[stack]: https://www.haskellstack.org/
[cabal]: https://haskell.org/cabal
[K Framework]: https://github.com/kframework/k
[curl]: https://curl.haxx.se/
[make]: https://www.gnu.org/software/make/
[direnv]: https://github.com/direnv/direnv
[haskell-language-server]: https://github.com/haskell/haskell-language-server
[language server]: https://langserver.org/
[hlint]: https://github.com/ndmitchell/hlint
[kore.cachix.org]: https://kore.cachix.org/
[Nix]: https://nixos.org
[entr]: https://github.com/eradman/entr
[fd]: https://github.com/sharkdp/fd
