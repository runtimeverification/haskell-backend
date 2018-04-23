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
