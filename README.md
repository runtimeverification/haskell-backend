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

The `/src` directory contains a parser for the Kore language implemented
in scala.

The `/src/test` directory contains a collection of Kore definition examples.

## Build Dependencies

-   [curl](https://curl.haxx.se/) and [jq](https://stedolan.github.io/jq/) for downloading and building latest nightly K.
-   [git](https://git-scm.com/) for checkstyle on the repository history and files.
-   [stack](https://www.haskellstack.org/) for building the Kore project using `make`.

Example installation of dependencies on Ubuntu:

```sh
sudo apt install curl jq git haskell-stack
```
