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


### Prover API proposal

Update: 3/1/18

One discussed way to expose the functioning of the API can be via a strategy language. The prover only deals with proof objects.
The api is simple - a function that takes a proof object, and a string in the strategy language. The returned value is another proof
object. The language also allows us to add new functionality/tactics to the prover, without directly changing the API as such. We
just extend the language.

### Strategy Language

-   The above functions can be expressed via use of a flexible strategy language, that the ML prover understands.
-   The language is rich enough to express proof tactics. So step would be a tactic for a proof that find the obligation that you're trying to prove.
    The backend is free to chose an algorithm that produces the right proof. In the step case, we can have multiple algorithms to find the next step.
    One has been discussed multiple times in the FSL meetings, and can be used by the Maude reference backend. This reduces the information presented to
    the user of the ML prover. The algorithm for step itself involves multiple ML proofs, which the prover will keep track of.
-   The clients of the prover would not like to deal with the prover's state, but have their own state (for instance, the debugger keeps track of user history).
    A proposed solution is that the prover has a data-structure for the proof object. The prover will always operates over proof objects. The proof object
    will have enough information to -

    -   Check the proof.
    -   Store any meta-data needed for quick-initialization.
    -   Use the information to produce a new proof object.
    -   Can be used outside to pretty print the proof, e.t.c.

    These proof objects, in conjunction with the strategy language simplify the API multifold. The prover becomes an interpreter for the strategy language. Keep
    in mind this interpreter is operating over a language dealing with proof objects. The interactive debugger becomes a "debugger" for this strategy language.
-   One natural question is why do we need two languages - one the prover understands, and another that the debugger understands. There are two possible approaches here -
    1   Make the strategy language rich enough for things beyond just proving (like step, e.t.c.). This makes the language itself complicated.
    2   The strategy language remains simple. The debugger has its own language that's catered to debugging. The analogy would be C and gdb.


## Steps to implement

-   Decide on strategy language grammar, semantics. We don't need a running interpreter, just need the
    grammar and semantics down, and we can parallelize.
-   Decide on data structures for proof objects. Again, need not be implemented. We just need what the
    components would be parallelize the debugger/pretty-printer e.t.c.
-   Decide to data structure for storing execution tree.
    -   Must store pattern id on the nodes, and have a mapping from pattern id to pattern.
    -   Must be able to represent subsumed, terminal and current state.
-   Decide on split of commands between REPL and the prover.
-   Build prototype REPL that works with dummy prover API.

