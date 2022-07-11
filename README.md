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
[/docs/introduction.md](https://github.com/runtimeverification/haskell-backend/blob/master/docs/introduction.md)
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

### macOS

Currently, LLVM 13 from Homebrew installs an incompatible version of
`install_name_tool`, which breaks the Haskell backend build on macOS. To resolve
this, uninstall `llvm` and install `llvm@12` from Homebrew, then build from
scratch.

#### Apple Silicon

If you are building the project on an Apple Silicon machine, a temporary
workaround is necessary to install a new enough version of GHC with support for
ARM64 Darwin. To do so, follow the instructions in [this
comment](https://github.com/commercialhaskell/stack/pull/5562#issuecomment-913015550).
The command-line flags for `stack` should then be specified _everywhere_ an
execution of `stack` is required. For `make` invocations in this project, set
the environment variable `STACK_BUILD_OPTS=--compiler ghc-8.10.7 --system-ghc`.

When `stack` and `ghc` merge their full support for ARM64 Darwin in future
releases, it should be possible to remove this workaround.

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

To build and run nix based packages at RV, please follow these instructions to set up nix:

_We are switching to using [nix flakes](https://nixos.wiki/wiki/Flakes) in all our repos. What this means at a high level is that some of the commands for building packages look a bit different._

To set up nix flakes you will need to install `nix` 2.4 or higher.If you are on a standard Linux distribution, such as Ubuntu, first [install nix](https://nixos.org/download.html#download-nix)
and then enable flakes by editing either `~/.config/nix/nix.conf` or `/etc/nix/nix.conf` and adding:

```
experimental-features = nix-command flakes
```

This is needed to expose the Nix 2.0 CLI and flakes support that are hidden behind feature-flags. (If you are on a different system like nixOS, see instructions for enabling flakes here: https://nixos.wiki/wiki/Flakes)

By default, Nix will build any project and its transitive dependencies from source, which can take a very long time. We therefore need to set up some binary caches to speed up the build
process. First, install cachix

```
nix-env -iA cachix -f https://cachix.org/api/v1/install
```

and then add the `kore` cachix cache

```
cachix use kore
```

Next, we need to set up the cache for our haskell infrastructure, by adding the following sections to `/etc/nix/nix.conf` or, if you are a trusted user, `~/.config/nix/nix.conf` (if you don't know what a "trusted user" is, you probably want to do the former):

```
trusted-public-keys = ... hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=
substituters = ... https://cache.iog.io
```

i.e. if the file was originally

```
substituters = https://cache.nixos.org
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY=
```

it will now read

```
substituters = https://cache.nixos.org https://cache.iog.io
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=
```


### Nix dev shell

We provide a `shell.nix` expression with a suitable development environment and
a binary cache at [runtimeverification.cachix.org]. The development environment is intended to
be used with `nix-shell` and `cabal`.

When the `.cabal` package description file changes, run:


```
# Requires Nix with flakes enabled.
nix run .#update-cabal
```

or

```
# Requires Nix to be installed.
./nix/rematerialize.sh
```

This script is also run by an automatic workflow.

### New GHC 9.2.3 dev shell

In order to make use of the new profiling options in GHC 9.2, we've added a nix shell which builds kore with GHC 9.2.3, to open the shell, run

```
nix develop .#ghc9
```

Then, use stack to build against `stack-nix-ghc9.yaml`:

```
stack --stack-yaml stack-nix-ghc9.yaml build
```

If you modified the `kore.cabal` file and want to build with GHC 9, you will have to run

```
# Requires Nix with flakes enabled.
nix run .#update-cabal-ghc9
```


### Integration tests

We provide a `test.nix` for running integration tests:

``` sh
nix-build test.nix  # run all integration tests
nix-build test.nix --argstr test imp  # run the integration tests in test/imp
nix-shell test.nix  # enter a shell where we can run tests manually
```

You can also us a new nix flake shell feature to compile the K framework against your current version of haskell backend and bring K into scope of your current shell via

```
nix shell github:runtimeverification/k/<commit> --override-input haskell-backend $(pwd)
```

where `<commit>` can be empty or point to a specific version of the K framework github repository. Running this command will add all of the K binaries like `kompile` or `kast` into the `PATH` of your current shell (this is not permanent and will only persist in your current shell window until you close it).


[docs]: https://github.com/runtimeverification/haskell-backend/tree/master/docs
[git]: https://git-scm.com/
[stack]: https://www.haskellstack.org/
[cabal]: https://haskell.org/cabal
[K Framework]: https://github.com/runtimeverification/k
[curl]: https://curl.haxx.se/
[make]: https://www.gnu.org/software/make/
[direnv]: https://github.com/direnv/direnv
[haskell-language-server]: https://github.com/haskell/haskell-language-server
[language server]: https://langserver.org/
[hlint]: https://github.com/ndmitchell/hlint
[runtimeverification.cachix.org]: https://runtimeverification.cachix.org/
[Nix]: https://nixos.org
[entr]: https://github.com/eradman/entr
[fd]: https://github.com/sharkdp/fd
