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
You may pass `--fast` to `stack build` or `-O0` to `cabal build` in order to
disable compiler optimizations and make build faster at the cost of slower runtime.

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

You can install/have access to K by either:
  * using [kup]
  * using a pre-built binary (see the releases page in the K repository)
  * if you use Nix, see the section below
  * using the `Dockerfile` to run the integration tests inside a container
  * or by just building K from source

### Running integration tests with Docker

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
- [ghcup] or [Nix] for managing required Haskell tooling
- [hlint] for compliance with project guidelines.
- [entr] and [fd] for running `./entr.sh` to keep important files up-to-date.

We recommend to keep `./entr.sh` running in the background
to keep important files (such as package descriptions) up-to-date,
especially if the developer is using Cabal.

### Running Haskell Language Server

[ghcup] provides a straight-forward way of installing the language server,
if you prefer to use [Nix] please refer to the relevant resources on how to
set up your [Nix] environment to build the server.
**Note**: HLS has to be built with the project's GHC version.

Prequisite: build the project with either Stack or Cabal.

Instructions on integrating with VSCode:
1. Install the [Haskell extension] 
2. Go to `Extension Settings` and pick `GHCup` in the `Manage HLS` dropdown
3. (Optional) Manually set the GHCup executable path
4. (Extra) Set `Formatting Provider` to `fourmolu` for correct formatting

### Developing with Nix

To build and run nix based packages at RV, please follow these instructions to set up nix:

_We are switching to using [nix flakes](https://nixos.wiki/wiki/Flakes) in all our repos. What this means at a high level is that some of the commands for building packages look a bit different._

To set up nix flakes you will need to install `nix` 2.4 or higher.If you are on a standard Linux distribution, such as Ubuntu, first [install nix](https://nixos.org/download.html#download-nix)
and then enable flakes by editing either `~/.config/nix/nix.conf` or `/etc/nix/nix.conf` and adding:

```
experimental-features = nix-command flakes
```

Note that if this is your first time using [Nix] you will have to manually create one of the `.conf` files.

This is needed to expose the Nix 2.0 CLI and flakes support that are hidden behind feature-flags. (If you are on a different system like nixOS, see instructions for enabling flakes here: https://nixos.wiki/wiki/Flakes)

By default, Nix will build any project and its transitive dependencies from source, which can take a very long time. We therefore need to set up some binary caches to speed up the build
process. First, install cachix

```
nix profile install github:cachix/cachix/v1.1
```

and then add the `k-framework` cachix cache

```
cachix use k-framework
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

Make sure that the file wasn't overwritten, if it was add the `experimental-features` again.

### Formatting
The CI requires all Haskell files to be formatted via [fourmolu](https://hackage.haskell.org/package/fourmolu).

If using VSCode, please refer to the language server section above. If not, the easiest way to do this locally is to run

```
nix run .#format
```

This will format all the haskell files in the given folder and all sub-folders. You can `cd` into a particular subfolder and run the command there, or if you only want to format a specific file, you can provide it as an argument to the above command:

```
nix run .#format Foo.hs
```

### Nix dev shell

We provide a development nix shell with a suitable development environment and
a binary cache at [runtimeverification.cachix.org]. The development can be launched via `nix develop` and then calling `stack build/test/etc`.

When the `kore.cabal` package description file changes, run:


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

### New GHC 9.2.5 dev shell

In order to make use of the new profiling options in GHC 9.2, we've added a nix dev shell which builds kore with GHC 9.2.5. To open the shell, run

```
nix develop .#ghc9
```

Then, use stack to build:

```
stack build
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
[kup]: https://github.com/runtimeverification/k/releases/latest 
[ghcup]: https://www.haskell.org/ghcup/
[Haskell extension]: https://marketplace.visualstudio.com/items?itemName=haskell.haskell
