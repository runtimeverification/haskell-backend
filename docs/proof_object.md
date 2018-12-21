# Proof Object Syntax

The following is a syntax to output a proof object.

```
  <ProofObject>  ::= <AssumedClaim>* <DerivedClaim>*

  <AssumedClaim> ::= <Id> : <Pattern>

  <DerivedClaim> ::= <Id> : <Pattern> by <ProofRule>

  <ProofRule>    ::=
  | propositional1(<Pattern>, <Pattern>)
  | propositional2(<Pattern>, <Pattern>, <Pattern>)
  | propositional3(<Pattern>, <Pattern>)
  | mp(<Id>, <Id>)
  | ug(<Variable>, <Id>)
  | varsubst(<Variable>, <Pattern>, <Variable>)
  | forall(<Variable>, <Pattern>, <Pattern>)
  | frame(<Id>, <Symbol>, <Position>)
  | propagate-bot(<Symbol>, <Position>)
  | propagate-or(<Symbol>, <Position>, <Pattern>, <Pattern>)
  | propagate-exists(<Symbol>, <Position>, <Variable>, <Pattern>)
  | existence(<Variable>)
  | singvar(<Variable>, <Pattern>, <PathPosition>, <PathPosition>)
  | <DerivedProofRule>
  
  <Id> ::= /* Quite flexible syntax. */
  
  <Position> ::= <PositiveInteger> /* 1, 2, 3, ... */
  
  <PathPosition> ::= /* A nonempty sequence of <Position> */


  <DerivedProofRule> ::=
  |  eqsubst-rule(<Id>, <Pattern>, <PathPosition>)          /* Equality Substituion Rule */
  |  funsubst(<Variable>, <Pattern>, <Variable>, <Pattern>) /* Functional Substituion */
  |  funsubst-rule(<Id>, <Id>)                              /* Functional Substituion Rule */
  |  eq-comm(<Id>)                                          /* Equality Commutativity */
  |  eq-trans(<Id>, <Id>)                                   /* Equality Transitivity*/

```

## Arguments in `<ProofRule>` and Their Meaning

We informally explain what the arguments in `<ProofRule>` mean.
In matching logic proof system, we have 12 proof rules.
Three of them are inference rules with one or more premises.
The rest nine are axiom schemas.
The three inference rules need `<Id>` arguments to refer to the premises
that they are applied on.
All 12 proof rules contain some meta-variables,
and the `<Pattern>`, `<Symbol>`, ... arguments tell us how to instantiate
these meta-variables in proof rules.

In the following, we list the correspondence between meta-variables in
proof rules and the arguments in `<ProofRule>`.

```
  |- P -> (Q -> P)
  propositional1(P, Q)

  |- (P -> Q -> R) -> (P -> Q) -> (P -> R)
  propositional2(P, Q, R)

  |- (not P -> not Q) -> (Q -> P)
  propositional3(P, Q)

  |- P and |- P -> Q implies |- Q
  mp(id1, id2) where id1 : P and id2 : P -> Q

  |- P implies |- forall x . P
  ug(x, id) where id : P

  |- (forall x . P) -> P[y/x]
  varsubst(x, P, y)

  |- (forall x . P -> Q) -> P -> forall x . Q
  forall(x, P, Q)
 
  |- P -> Q implies |- sigma(..., P, ...) -> sigma(..., Q, ...)
  frame(id1, sigma, k)
  where P and Q appear as the kth arguments.

  |- sigma(..., bot, ...) -> bot
  propagate-bot(sigma, k)
  where bot is the kth argument.

  |- sigma(..., P \/ Q, ...) -> sigma(..., P, ...) \/ sigma(..., Q, ...)
  propagate-or(sigma, k, P, Q)
  where P \/ Q, P, Q are the kth arguments resp.

  |- sigma(..., exists x . P, ...) -> exists x . sigma(..., P, ...)
  propagate-exists(sigma, k, x, P)
  where (exists x . P) and P are the kth arguments resp.

  |- exists x . x
  existence(x)

  |- not (C1[x /\ P] /\ C2[x /\ not P])
  singvar(x, P, pos1, pos2)
  where `x /\ P` occurs at position `pos1` in `C1`,
  and `x /\ not P` occurs at position `pos2` in `C2`.

  /* Derived Proof Rules */

  |- P = Q implies |- C[P] = C[Q]
  eqsubst-rule(id, C, pos)
  where `C` is any context,
  and `P` and `Q` occur at position `pos` in `C`.

  |- (exists t . P1 = t) /\ (forall x . P2) -> P2[P1/t]
  funsubst(t, P1, x, P2)

  |- exists t . P1 = t and |- forall x . P2 implies |- P2[P1/t]
  funsubst-rule(id1, id2)

  |- P = Q implies |- Q = P
  eq-comm(id1)

  |- P = Q and |- Q = R implies |- P = R
  eq-trans(id1, id2)

```

## How to check if a `<ProofObject>` is correct?

We need a proof checker.

There are some global conditions that the proof checker should check, as well
as some local conditions that the proof checker should check for every proof
step.
There are also assumptions about the proof objects in order to make proof
checking very easy.

### Assumptions that make proof checking very easy.
We are generous to have various assumptions that make the
proof checker extremely simple.
* All bound variables are different throughout the proof object;
  (Is it even practical?)
* (Please add more items to this list)

### Global conditions that the checker should check

* Unique Ids for claims;
* (Please add more items to this list)

### Local conditions that the checker should check for every proof step

#### `id : Pattern by propositional1(P, Q)`
* Check that `Pattern` is syntactically equal to `P -> (Q -> P)`

#### `id : Pattern by propositional2(P, Q, R)`
* Check that `Pattern` is syntactically equal to
  `(P -> Q -> R) -> (P -> Q) -> (P -> R)`

#### `id : Pattern by propositional3(P, Q)`
* Check that `Pattern` is syntactically equal to
  `(not P -> not Q) -> (Q -> P)`

#### `id : Pattern by mp(id1, id2)`
* Grab from the previous claims `id1 : P1` and `id2 : P2`
* Check that `P2` is syntactically equal to
  `P1 -> Pattern`

#### `id : Pattern by ug(x, id1)`
* Grab from the previous claims `id1 : P`
* Check that `Pattern` is syntactically equal to
  `forall x . P`

#### `id : Pattern by varsubst(x, P, y)`
* Check that `y` doesn't have bound occurrence in `P`
* Check that `Pattern` is syntactically equal to
  `(forall x . P) -> P[y/x]`

#### `id : Pattern by forall(x, P, Q)`
* Check that `Pattern` is syntactically equal to
  `(forall x . P -> Q) -> P -> forall x . Q`
* Check that `x` does not occur free in `P`

#### `id : Pattern by frame(id1, sigma, k)`
* Grab from the previous claims `id1 : Pattern1`
* Check that `Pattern1` has the form `Left1 -> Right1`
* Check that `Pattern`  has the form `Left -> Right`
* Check that `Left` and `Right` both have the form `sigma(...)`
* For each `i = 1 ... N` where `N` is the number of arguments in `Left`
* --- Grab the ith argument of `Left` and `Left`, denoted as `Pi` and `Qi`
* --- if `i` is not `k`
* ------ Check that `Pi` is syntactically equal to `Qi`
* --- else
* ------ Check that `Pi` is syntactically equal to `Left1`
* ------ Check that `Qi` is syntactically equal to `Right1`

#### `id : Pattern by propagate-bot(sigma, k)`
* Check that `Pattern`  has the form `Left -> Right`
* Check that `Left` has the form `sigma(...)`
* Grab the kth argument of `Left`, denoted as `P`
* Check that `P` is syntactically equal to `bot`
* Check that `Right` is syntactically equal to `bot`

#### `id : Pattern by propagate-or(sigma, k, P, Q)`
* Check that `Pattern`  has the form `Left -> (RightA \/ RightB)`
* Check that `Left`, `RightA`, `RightB` all have the form `sigma(...)`
* For each `i = 1 ... N` where `N` is the number of arguments in `Left`
* --- Grab the ith argument of `Left`, `RightA`, `RightB`
  --- and denote them as `Li`, `RAi`, and `RBi`
* --- if `i` is not `k`
* ------ Check that `Li`, `RAi`, and `RBi` are syntactically equal
* --- else
* ------ Check that `Li` is syntactically equal to `P \/ Q`
* ------ Check that `RAi` is syntactically equal to `P`
* ------ Check that `RBi` is syntactically equal to `Q`

#### `id : Pattern by propagate-exists(sigma, k, x, P)`
* Check that `Pattern`  has the form `Left -> Right`
* Check that `x` doesn't occur free in `Left`
* Check that `Left` has the form `sigma(...)`
* Check that `Right` has the form `exists x . Q`
* Check that `Q` has the form `sigma(...)`
* For each `i = 1 ... N` where `N` is the number of arguments in `Left`
* --- Grab the ith argument of `Left`, `P`
  --- and denote them as `Li` and `Pi`
* --- if `i` is not `k`
* ------ Check that `Li` and `Pi` are syntactically equal
* --- else
* ------ Check that `Li` is syntactically equal to `exists x . P`
* ------ Check that `Pi` is syntactically equal to `P`

#### `id : Pattern by existence(x)`
* Check that `Pattern` is syntactically equal to `exists x . x`

#### `id : Pattern by singvar(x, P, pos1, pos2)`
* Check that `Pattern` has the form `not (C1 /\ C2)`
* Grab the subpattern at position `pos1` of `C1`, denoted as `P1`
* Grab the subpattern at position `pos2` of `C2`, denoted as `P2`
* Check `P1` has the form `x /\ P`
* Check `P2` has the form `x /\ not P`
* Check the path to `pos1` in `C1` contains only symbols
* Check the path to `pos2` in `C2` contains only symbols

#### `id : Pattern by eqsubst-rule(id1, C, pos)`
* Grab from the previous claims `id1 : Pattern1`
* Check that `Pattern1` has the form `P = Q`
* Check that `Pattern` has the form `Left = Right`
* Substitute at `pos` in `C` the pattern `P` and obtain `CP` /* purely term substitution, no implicit alpha-renaming, no occur-free checking */
* Substitute at `pos` in `C` the pattern `Q` and obtain `CQ` /* purely term substitution, no implicit alpha-renaming, no occur-free checking */
* Check that `Left` and `CP` are syntactically equal
* Check that `Right` and `CQ` are syntactically equal

#### `id : Pattern by funsubst(t, P1, x, P2)`
* Check that all free variables in `P1` has no bound occurrence in `P2`
* Check that `Pattern` has the form `EP /\ FP -> CP`
* Check that `EP` equals `exists t . P1 = t`
* Check that `FP` equals `forall x . P2`
* Check that `CP` equals `P2[P1/t]`

#### `id : Pattern by funsubst-rule(id1, id2)`
* Grab `id1 : Pattern1` and `id2 : Pattern2`
* Check that `Pattern1` has the form `exists t . P1 = t`
* Check that `Pattern2` has the form `forall x . P2`
* Check that all free variables in `P1` has no bound occurrence in `P2`
* Check that `Pattern` has the form `P2[P1/t]`

#### `id : Pattern by eq-comm(id1)`
* Grab `id1 : Pattern1`
* Check that `Pattern1` has the form `P = Q`
* Check that `Pattern` has the form `Q = P`

#### `id : Pattern by eq-trans(id1,id2)`
* Grab from the previous claims `id1 : P1`
* Grab from the previous claims `id2 : P2`
* Check that `P1` has the form `P11 = P12`
* Check that `P2` has the form `P21 = P22`
* Check that `Pattern` has the form `Q1 = Q2`
* Check that `P11` is syntactically equal to `Q1`
* Check that `P12` is syntactically equal to `P21`
* Check that `P22` is syntactically equal to `Q2`

# Mixed-level Proof Object Syntax

Language definitions are expected to use mostly
object-level or mixed-level patterns, which is why
we have defined the Kore syntax to allow such patterns,
rather than simply requiring everything to be encoded
as meta-level patterns.
For the same reason, we wish to define a syntax of proofs
that allows writing mixed-level patterns, and that allows
object-level reasoning steps to be written in the
form `by <ProofRule>` rather than by explicitly
constructing meta-level proofs of patterns involving `#provable`
using the hypotheses described in section 7.7 of
The Semantics of K.

To support this we allow as patterns any Kore pattern,
which follows the syntax of `<pattern>` in 9.1.4.
```
  <ProofObject>  ::= <AssumedClaim>* <DerivedClaim>*

  <AssumedClaim> ::= <Id> : <Pattern>

  <DerivedClaim> ::= <Id> : <Pattern> by <ProofRule>

  <Id> ::= /* Quite flexible syntax. */
```

Proofs will be defined so that a valid mixed-level proof can
be transformed into a valid simple proof that assumes or
proves (resp.) the lifting of each assumed or derived claim
of the mixed-level proof.

The patterns in claims will be use a special "claim lifting" that
transforms a pattern `phi` whose topmost element is an meta-level
construct into the pure meta pattern `[[phi]]`, and lifts
a pattern which has an object-level construct as the topmost element
and has no metavariables into the pure meta pattern `#provable([[phi]])`.

The claim lifting of a pattern that has metavariables needs to be defined
in detail, but it will generally add implications before `#provable([[phi]])`
asserting that the metavariables are instantiated with well-formed
sorts or object patterns.

Following the conventions of lifting we the meta-level proof rules
will have a '#' prefix added to the name of the object-level proof rules.
All the same proof rules that we have above for the meta-level should
have object-level versions as well, but expanding the object-level
proof to a pure matching logic proof will involve instantiating and
using hypotheses about `#provable` rather than using matching logic
proof rules directly.
Compared to the previous section, the meta-level proof rules are
generalized slightly by allowing mixed patterns in the arguments,
which are uniformly interpreted as their lifting
(`#provable` is not automatically added).
So that object-level proof rules have the same arity as
meta-level proof rules, any hypotheses about `#wellFormed`
or `#occursFree` are automatically discharged.

* TODO: Need to explain how variables or quantifiers resulting
from lifting of metavariables are handled by object-level proof rules.
I think the object-level proof rules should be defined to handle
at least simple cases automatically.

To give the user access to this same automation,
additional meta-level proof rules are provided.
The new proof rule `#check-well-formed(P)` proves
that `#wellFormed` holds of the lifting of P whenever
P is well-formed.
Similarly, `#check-free(x,P)` and `#check-not-free(x,P)`
respectively deduce patterns  `#occursFree{s}(x,P)`
or `\not{s}(#occursFree{s}(x,P))` when they are true.

```
  <MixedProofObject>  ::= <AssumedClaim>* <DerivedClaim>*

  <AssumedClaim> ::= <Id> : <Pattern>

  <DerivedClaim> ::= <Id> : <Pattern> by <MixedProofRule>

  <Id> ::= /* Quite flexible syntax. */
  <Position> ::= <PositiveInteger> /* 1, 2, 3, ... */
  <PathPosition> ::= /* A nonempty sequence of <Position> */

  <MixedProofRule>    ::=
  | <ObjectProofRule>
  | <MetaProofRule>

  <ObjectProofRule>    ::=
  | propositional1(<Pattern>, <Pattern>)
  | propositional2(<Pattern>, <Pattern>, <Pattern>)
  | propositional3(<Pattern>, <Pattern>)
  | mp(<Id>, <Id>)
  | ug(<Variable>, <Id>)
  | varsubst(<Variable>, <Pattern>, <Variable>)
  | forall(<Variable>, <Pattern>, <Pattern>)
  | frame(<Id>, <Symbol>, <Position>)
  | propagate-bot(<Symbol>, <Position>)
  | propagate-or(<Symbol>, <Position>, <Pattern>, <Pattern>)
  | propagate-exists(<Symbol>, <Position>, <Variable>, <Pattern>)
  | existence(<Variable>)
  | singvar(<Variable>, <Pattern>, <PathPosition>, <PathPosition>)
  | <DerivedObjectProofRule>

  <DerivedObjectProofRule> ::=
  |  eqsubst-rule(<Id>, <Pattern>, <PathPosition>)          /* Equality Substituion Rule */
  |  funsubst(<Variable>, <Pattern>, <Variable>, <Pattern>) /* Functional Substituion */
  |  funsubst-rule(<Id>, <Id>)                              /* Functional Substituion Rule */
  |  eq-comm(<Id>)                                          /* Equality Commutativity */
  |  eq-trans(<Id>, <Id>)                                   /* Equality Transitivity*/

  <MetaProofRule>    ::=
  | #propositional1(<Pattern>, <Pattern>)
  | #propositional2(<Pattern>, <Pattern>, <Pattern>)
  | #propositional3(<Pattern>, <Pattern>)
  | #mp(<Id>, <Id>)
  | #ug(<Variable>, <Id>)
  | #varsubst(<Variable>, <Pattern>, <Variable>)
  | #forall(<Variable>, <Pattern>, <Pattern>)
  | #frame(<Id>, <Symbol>, <Position>)
  | #propagate-bot(<Symbol>, <Position>)
  | #propagate-or(<Symbol>, <Position>, <Pattern>, <Pattern>)
  | #propagate-exists(<Symbol>, <Position>, <Variable>, <Pattern>)
  | #existence(<Variable>)
  | #singvar(<Variable>, <Pattern>, <PathPosition>, <PathPosition>)
  | <DerivedMetaProofRule>
  | <AutomaticMetaProofRule>

  <DerivedMetaProofRule> ::=
  |  #eqsubst-rule(<Id>, <Pattern>, <PathPosition>)          /* Equality Substituion Rule */
  |  #funsubst(<Variable>, <Pattern>, <Variable>, <Pattern>) /* Functional Substituion */
  |  #funsubst-rule(<Id>, <Id>)                              /* Functional Substituion Rule */
  |  #eq-comm(<Id>)                                          /* Equality Commutativity */
  |  #eq-trans(<Id>, <Id>)                                   /* Equality Transitivity*/

  <AutomaticMetaProofRule> ::=
  |  #check-well-formed(<Pattern>)
  |  #check-free(<Variable>,<Pattern>)
  |  #check-not-free(<Variable>,<Pattern>)
```
