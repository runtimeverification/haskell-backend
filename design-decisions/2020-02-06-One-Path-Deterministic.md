One-Path Reachability implemented only for deterministic semantics
==================================================================

Background
----------

Proving an one-path reachability formula `∀X.φ → ◇w ∃Y.ψ` means proving that,
for _all_ interpretations `ρ` for the variables in `X`, and all configurations
`γ` which are matched by `φ` under the interpretation `ρ`, there _exists_
a path from `γ` to a configuration `γ'` and an interpretation `ρ'` extending
`ρ` with values for the variables in `Y` such that `γ'` is matched by `ψ`
under the interpretation `ρ'`.

This is implemented as symbolically executing the configuration `φ`,
potentially coinductively using the formula itself as a rule, while
checking (at each step) whether a configuration matching `ψ` has been reached.

The problem
-----------

While all-path reachability requires one to find a configuration matching `ψ`
on _all_ paths and for _all_ instances of `φ`, one-path reachability requires
finding a configuration matching `ψ` on just _one_ path, but still for _all_
instances of `φ`.  This requires a double effort when exploring the space
of the symbolic execution because we have a disjunction (just one path is
required) of conjunctions (all instances of `φ` need to be accounted for).

Decision
--------

To maintain soundness while avoiding implementation complexity, we will assume
that the definition is (strongly) deterministic, i.e., there are no concurrent
transitions from the same state to different ones.

The one-path algorithm applies rewrite rules to the goals using the `deriveSeq`
procedure, which was not designed to consider rule applications where two or
more rules have the same left hand side (as in the case of non-deterministic semantics).
These characteristics of the implementation entail that the one-path algorithm,
while sound, doesn't guarantee full state space coverage.

This is in accord with the original definition of one-path reachability which
only guaranteed (relative) completeness for (strongly) deterministic
definitions, and with the fact that for non-deterministic definitions,
all-path reachability already provides a (relative) complete verification
procedure.

### Consequences

Although still sound for non-deterministic definitions, this decision might
lead to claims not being proved because the semantics has chosen the wrong path
(and would not explore the other paths).

#### Example 1

Given the following definition:
```
module PATH
  imports DOMAINS
  syntax S ::= "a" | "b" | "c"

  rule a => b
  rule a => c
endmodule
```

proving the one-path reachability claim `a => c` might be not possible,
if the prover selects to advance the execution using the other rule.

#### Example 2

Given the following definition:
```
module PATH
  imports DOMAINS
  syntax S ::= "a" | "b" | "c" 
  syntax Cmd ::= "select"

  configuration <k> .K </k> <state> .Set </state>

  rule <k> select => X ...</k> <state>... SetItem(X:S) ...</state>
endmodule
```

the one-path reachability claim 
```
<k> select => ?X </k> <state> SetItem(a) SetItem(b) SetItem(c) </state>
    ensures ?X ==K b orBool ?X ==K c 
```

might not be provable because the prover selects to advance the execution
using the `X=a` instance for the `select` rule.


Options
-------

We could devise an algorithm to perform a more exhaustive exploration of the
search-space.

We will just sketch it below on an example.

Consider the following specification
```
module TEST
  imports BOOL
  syntax S ::= "b" | "c" | "d" | "e"
             | test(Bool)
  
  test(true) => b   // first rule
  test(true) => c   // 2nd rule
  test(false) => d  // 3rd rule
  test(false) => e  // 4th rule
endmodule
```

together with the claim `test(X) => c \/ e`.

The idea would be to derive the goal in parallel with each of the rules,
but to associate a remainder to each particular derivation,
then we will require that the derived goal and the remainder need to be
satisfied simultaneously, but that any of thus obtained
derived goal - remainder pairs is sufficient to prove our original goal.

Thus, we would replace `test(X) => c \/ e` by the derivation
```
(
  b => c \/ e                     -- derivation using 1st rule
  /\
  test(X) /\ x <> true => c \/ e  -- remainder after applying 1st rule
)
\/
(
  c => c \/ e                     -- derivation using 2nd rule
  /\
  test(X) /\ x <> true => c \/ e  -- remainder after applying 2nd rule
)
\/
(
  d => c \/ e                     -- derivation using 3rd rule
  /\
  test(X) /\ x <> false => c \/ e -- remainder after applying 3rd rule
)
\/
(
  e => c \/ e                     -- derivation using 4th rule
  /\
  test(X) /\ x <> false => c \/ e -- remainder after applying 4th rule
)
```

then we can choose any goal in the or-and tree and expand it, and continue to do
so until all goals are stuck or one of the global disjuncts is completely proven.

For example, assuming a leftmost, innermost strategy, we could continue
by first checking `b => c \/ e` and declaring it stuck, meaning that we
can skip its remainder altogether, then moving to `c => c \/ e` which
holds without further expansion, so it can be eliminated, leading us to
its remainder `test(X) /\ x <> true => c \/ e`.

Following the algorithm, this can be expanded to
```
(
  d => c \/ e
  /\
  test(X) /\ x <> true /\ x <> false => c \/ e
)
\/
(
  e => c \/ e
  /\
  test(X) /\ x <> true /\ x <> false => c \/ e
)
```

Again, `d => c \/ e` is stuck, so we can skip to
`e => c \/ e`, which holds immediately, so it can be eliminated.
Its remainder, too, can be eliminated, as 
` x <> true /\ x <> false` is equivalent to `⊥`.

This concludes the proof, as we have found witnesses of reaching the
destination for all instances of the input.

### Note

When deriving goals, care should be taken about the same rule unifing in
multiple ways with the same configuration, as in the [Example 2](#example_2)
above. In such cases, each of the unification instances should be considered
as a separate rule instance when doing the parallel derivation, and thus a
separate remainder should be computed for each.

