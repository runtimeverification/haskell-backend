# Roadmap for the Haskell K REPL

This is a roadmap for implementing an interactive repl for the K prover, assuming
that the prover backend already exists.

This provides basic interactivity the ML prover, sufficient to reproduce the current
debugger's functionality.


## Example Interaction with the REPL

```
// Interactively load a K Definition
K> source <my-file.k>

// Determine the module we're working with
K> select <MY-MODULE>

// Set current pattern as PATTERN
K> load PATTERN

K> print

// Take n steps. Default value is 1.
K> step [n]
... Took n steps  ...


// Star (*) marks the current pattern
K> print tree
 S1
 | - n - S2 *

K> step [n2]
... Took n2 steps ...

K> print tree
 S1
 | - n - S2
         | - n2 - S3 *

// S3 is a disjunction, we want to split
// Defaults to current state, if unspecified
K> split [STATE_ID]
... Split STATE_ID ...

K> print tree
 S1
 | - n - S2
         | - n2 - S3.1 *
         | - n2 - S3.2
         | - n2 - S3.3

K> switch S3.2

K> print tree
 S1
 | - n - S2
         | - n2 - S3.1
         | - n2 - S3.2 *
         | - n2 - S3.3

K> subsumed? S2
... S3.2 subsumed by S2 ...

K> print tree
 S1
 | - n - S2
         | - n2 - S3.1
         | - n2 - S3.2 -> S2 *
         | - n2 - S3.3

K> switch S3.3

K> step
... Terminal State. 0 Steps taken ...

K> print tree
 S1
 | - n - S2
         | - n2 - S3.1
         | - n2 - S3.2 -> S2
         | - n2 - S3.3 (terminal) *

```


## Assumptions for Prover Backend (Expected functionality via API)

-   Step function - takes a pattern, gives the next pattern. We assume that
                    the function may return an arbitrary ML pattern.
-   Subsumption   - Given P1 and P2, check if P1 -> P2
-   Split         - Given an ML pattern, split it into a set of subpatterns,
                    s.t. their disjunction is equivalent to the original pattern.


## Steps to implement

-   Decide to data structure for storing execution tree.
    -   Must store pattern id on the nodes, and have a mapping from pattern id to pattern.
    -   Must be able to represent subsumed, terminal and current state.
-   Decide on split of commands between REPL and the prover.
-   Build prototype REPL that works with dummy prover API.

