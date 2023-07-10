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

You may pass `--fast` to `stack build` or `-O0` to `cabal build` in order to
disable compiler optimizations and make build faster at the cost of slower runtime.

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
- The [K Framework] frontend (its version should be the one stated in [/deps/k_release](https://github.com/runtimeverification/haskell-backend/blob/master/deps/k_release))
- Python 3.x with the [`jsonrpcclient`](https://github.com/explodinglabs/jsonrpcclient) library installed

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

### Running Haskell Language Server

[ghcup] provides a straightforward way of installing the language server,
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

_We are using [nix flakes](https://nixos.wiki/wiki/Flakes) in all our repos. What this means at a high level is that some of the commands for building packages look a bit different._

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

### Upgrading dependencies

When one of the package description files (`kore.cabal`, `kore-rpc-types.cabal`) changes, or when upgrading to a newer `stack` resolver, the dependencies need to be consolidated to avoid accidental breakage from incompatible up-stream updates. We use a `cabal.project.freeze` file to pin the dependencies to what the current `stack` resolver is using.

The script [`scripts/freeze-cabal-to-stack-resolver.sh`](https://github.com/runtimeverification/haskell-backend/tree/master/scripts/freeze-cabal-to-stack-resolver.sh) should do most of that work (the existing `freeze` file must be removed before running it), and [`scripts/check-cabal-stack-sync.sh`](https://github.com/runtimeverification/haskell-backend/tree/master/scripts/check-cabal-stack-sync.sh) checks the result. Some manual adjustments will still be necessary for the `nix` builds in CI and locally to work.

In addition, any GHC or resolver upgrades must double-check the `compiler-nix-name` and `index-state` values in the [`flake.nix`](https://github.com/runtimeverification/haskell-backend/blob/master/flake.nix#L41-L42) file.

### Integration tests

Haskell-backend provides an integration shell for running integration tests, which compile the K framework (of a specified version) against your current version of haskell backend and brings K into scope of your current shell. 

The integration shell is part of the `k` repository, but invoked from the local tree, adding additional tools (see [`nix/integration-shell.nix`](https://github.com/runtimeverification/haskell-backend/blob/master/nix/integration-shell.nix) and [`../k/flake.nix`](https://github.com/runtimeverification/k/blob/master/flake.nix#L180)). Its `haskell-backend` dependency must be overridden to use the `haskell-backend` dependency from the current checked-out tree, and the `k` version will usually be the one from `deps/k_release`.

To use this nix shell, execute

``` sh
me@somewhere:haskell-backend$ nix develop \
    github:runtimeverification/k/v$(cat deps/k_release)#kore-integration-tests \
    --override-input haskell-backend . --update-input haskell-backend
...
...(nix output)
integration-shell:me@somewhere:haskell-backend$
```

(This will take some time the first time you run it for a specific K framework version...)  
A specific commit or version tag of the K framework github repository can be used instead of `$(cat deps/k_release)`.

Running this command will add all of the K binaries like `kompile` or `kast` into the `PATH` of your current shell. This is not permanent and will only persist in your current shell window until you exit the active nix shell).

```
integration-shell:me@somewhere:haskell-backend$ make -C test/issue-3344 test
...
...(make output)
integration-shell:me@somewhere:haskell-backend$ exit
me@somewhere:haskell-backend$ 
```

            

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
