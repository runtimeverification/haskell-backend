Proving lemmas
==============

Background
----------

In order to prove rewrite claims, we usually need lemmas describing
the function symbols we use. As an example, we may have a lemma saying that the
length of a string is not negative, i.e.
```
rule length(S) > 0 => true
```

The lemmas that I have seen are, usually, given without proofs.

There is an effort by daejunpark and malturki to prove some properties
for Casper, simulating Coq-style proofs:
https://github.com/runtimeverification/beacon-chain-verification/tree/static-model-coq-specs-dependencies/casper/k

Summary
-------

This document attempts to provide some hints about how to prove the lemmas we
use for various semantics, in a way similar to what daejunpark and malturki
did, but in a simpler and less powerful way. Hopefully, proofs done this way
do not require many additional features from the frontend and backend,
and can be later transformed into full proofs (which may require additional
features).

These proofs would need the following:

* Ideally, an induction engine. Practically, at least in the beginning:
  * we would find a set of symbols that generate a sort
    (e.g. `0` and `\x -> x+1` for natural numbers, initially without any proof)
  * we would provide an induction hypothesis
  * we would provide some claims based on that hypothesis
    (`k` macros would be nice)
  * the Haskell backend would check the claims.
  * we could try to become more rigorous in the future.
* Some tools to direct proofs
  * Marking rules as concrete / not concrete for a single proof
  * Providing hints about which splits are allowed
    * most of these can be done manually, in the specification, but there are
      other ways.

Example 1
---------

We have the following definition, taken from the evm repository:
```
syntax Bytes ::= "nilBytes"
               | Int ":" Bytes

syntax Int ::= lengthBytes(Bytes)
               [function, total, smtlib(lengthBytes)]
syntax Int ::= lengthBytes(Bytes, Int)
               [function, klabel(lengthBytesAux), smtlib(lengthBytesAux)]
rule lengthBytes(BS) => lengthBytes(BS, 0)
rule lengthBytes(nilBytes, SIZE) => SIZE
rule lengthBytes(B : BS, SIZE) => lengthBytes(BS, SIZE +Int 1)
```

And we would like to prove the following lemmas:

```
rule lengthBytes(BS, i) ==Int i +Int lengthBytes(BS)
rule lengthBytes(BS) >=Int 0 => true
rule lengthBytes(B:BS) ==Int 1 +Int lengthBytes(BS)
```
We would prove them by induction on BS. The set of constructors/generators, is,
of course, `nilBytes` and `:`.

Let’s start with the first claim. We can write it as
```
forall BS . forall i . lengthBytes(BS, i) ==Int i +Int lengthBytes(BS)
```
We will prove it by structural induction on `BS`. To do that, let us define
a macro:
```
P(i, BS) :=  lengthBytes(BS, i) ==Int i +Int lengthBytes(BS)
```

Next, we will attempt to prove `forall i . P(i, nilBytes)` and
`P(i, B:BS) if (forall j . P(j, BS))`.
To do that, we will use the following rewrite rule: `start(X) => end(X)`
and the following hand-written claims:
```
start(P(i, nilBytes)) => end(true)
start(P(i, B:BS)) => end(true)
    if P(i + 1, BS) and P(1, BS)
```

The backend will prove them like this:
```
start(P(i, nilBytes))
  = start(lengthBytes(nilBytes, i) ==Int i +Int lengthBytes(nilBytes))
  = start(i ==Int i +Int lengthBytes(nilBytes, 0))
  = start(i ==Int i +Int 0)
  = start(true)
  => end(true)
```
and
```
start(P(i, B:BS)) and P(i + 1, BS) and P(1, BS)
  = start(lengthBytes(B:BS, i) ==Int i +Int lengthBytes(B:BS))
        and  lengthBytes(BS, i + 1) ==Int i + 1 +Int lengthBytes(BS))
        and  lengthBytes(BS, 1) ==Int 1 +Int lengthBytes(BS))
  = start(lengthBytes(BS, i + 1) ==Int i + lengthBytes(B:BS, 0) )
        and  lengthBytes(BS, i + 1) ==Int i + 1 +Int lengthBytes(BS))
        and  lengthBytes(BS, 1) ==Int 1 +Int lengthBytes(BS))
  = start(lengthBytes(BS, i + 1) ==Int i + lengthBytes(BS, 1) )
        and  lengthBytes(BS, i + 1) ==Int i + 1 +Int lengthBytes(BS))
        and  lengthBytes(BS, 1) ==Int 1 +Int lengthBytes(BS))
  => end(lengthBytes(BS, i + 1) ==Int i + lengthBytes(BS, 1) )
        and  lengthBytes(BS, i + 1) ==Int i + 1 +Int lengthBytes(BS))
        and  lengthBytes(BS, 1) ==Int 1 +Int lengthBytes(BS))
```
And the SMT solver will be able to check that this is the expected result.

If we have this, we can try proving the second lemma. We will start by adding
the first lemma as a SMT lemma, since it was proven, then we will continue as
before, by defining a macro: `P(BS) := lengthBytes(BS) >=Int 0`,
and we will attempt to prove `hypothesis(nilBytes)` and
`P(B:BS) if P(BS)`. We will use the same rewrite rule:
`start(X) => end(X)` and the following claims:

```
start(P(nilbytes)) => end(true)
start(P(B:BS)) => end(true) if P(BS)
```

The backend will prove the first one like this:
```
start(P(nilbytes))
   = start(lengthBytes(nilBytes) >=Int 0))
   = start(lengthBytes(nilBytes, 0) >=Int 0)
   = start(0 >=Int 0)
   = start(true)
   => end(true)
```
And the second one like this:
```
start(P(B:BS)) and P(BS)
  = start(lengthBytes(B:BS) >=Int 0) and lengthBytes(BS) >=Int 0
  = start(lengthBytes(B:BS, 0) >=Int 0) and lengthBytes(BS, 0) >=Int 0
  = start(lengthBytes(BS, 1) >=Int 0) and lengthBytes(BS, 0) >=Int 0
  => end(lengthBytes(BS, 1) >=Int 0) and lengthBytes(BS, 0) >=Int 0
```
And the SMT solver should, hopefully, be able to apply the second lemma,
`lengthBytes(BS, i) ==Int i +Int lengthBytes(BS)`, to prove this one.

The third one should be trivial.

Example 2
---------

We assume the third lemma above as a simplification lemma. We will also assume
that the `lengthBytes` rules are marked as concrete. We will need a way to make
sure that `substrBytes(BS, 0, lengthBytes(BS)) == BS` does not become a
substitution.

Definition:
```
syntax Bytes ::= "nilBytes"
               | Int ":" Bytes

syntax Bytes ::= substrBytes(Bytes, Int, Int) [function]
rule substrBytes(BS, 0, 0) => nilBytes
rule substrBytes(B : BS, N, M) =>
    substrBytes(BS, N -Int 1, M -Int 1) requires N >Int 0
rule substrBytes(B : BS, 0, M) =>
    B : substrBytes(BS, 0, M -Int 1) requires M >Int 0
```

We want to prove

```
substrBytes(BS, 0, N) = BS if N == lengthBytes(BS)
```

The induction hypothesis is
```
P(BS) := substrBytes(BS, 0, lengthBytes(BS)) == BS
```
We want to prove `P(nilBytes)` and
`P(B:BS) if P(BS)`. We will have the same
`start(X) => end(X)` production as above. These are the hand-written `k` rules
that we will prove:
```
rule start(P(nilBytes)) => end(true)
rule start(P(B:BS)) => end(true) if P(BS)
```

The Haskell backend will prove them like this:
```
start(P(nilBytes))
  = start(substrBytes(nilBytes, 0, lengthBytes(nilBytes)) == nilBytes)
  = start(substrBytes(nilBytes, 0, 0) == nilBytes)
  = start(nilBytes == nilBytes)
  = start(true)
  => end(true)
```
and
```
start(P(B:BS)) and P(BS)
  = start(substrBytes(B:BS, 0, lengthBytes(B:BS)) == B:BS)
        and substrBytes(BS, 0, lengthBytes(BS)) == BS
  = start(substrBytes(B:BS, 0, 1 + lengthBytes(BS)) == B:BS)
        and substrBytes(BS, 0, lengthBytes(BS)) == BS
  = start(B : substrBytes(BS, 0, 1 + lengthBytes(BS) - 1) == B:BS)
        and substrBytes(BS, 0, lengthBytes(BS)) == BS
  // Hopefully equals simplification can help us, otherwise we need another
  // lemma.
  = start(substrBytes(BS, 0, 1 + lengthBytes(BS) - 1) == BS)
        and substrBytes(BS, 0, lengthBytes(BS)) == BS
  => end(substrBytes(BS, 0, 1 + lengthBytes(BS) - 1) == BS)
        and substrBytes(BS, 0, lengthBytes(BS)) == BS
```
And the SMT can hopefully solve this.

Example 3
---------

This is an actual lemma from the evm repository.

We will assume the following lemma:
```
Bytes2Int(B:BS, BE, Unsigned) =
   B *Int (256 ^ length(BS)) + Bytes2Int(BS, BE, Unsigned)
```

And the following definition:
```
syntax Int ::= #asWord ( ByteArray ) [function, smtlib(asWord)]
rule #asWord(WS) => chop(Bytes2Int(WS, BE, Unsigned))

syntax Int ::= chop ( Int ) [function, total, smtlib(chop)]
rule chop ( I:Int ) => I modInt pow256 [concrete, smt-lemma]

syntax Int ::= Int "modInt" Int
    [function, klabel(modInt), symbol, left, smt-hook(mod), hook(INT.emod)]
syntax Int ::= Bytes2Int(Bytes, Endianness, Signedness)
    [function, total, hook(BYTES.bytes2int)]

syntax Bytes ::= "nilBytes"
               | Int ":" Bytes

syntax Bytes ::= #drop ( Int , Bytes )
    [klabel(dropBytes), function, total]
rule #drop(N, BS:Bytes) => BS
    requires notBool N >Int 0
rule #drop(N, BS:Bytes) => .Bytes
    requires notBool lengthBytes(BS) >Int 0 andBool N >Int 0
rule #drop(N, BS:Bytes) => .Bytes
    requires lengthBytes(BS) >Int 0 andBool N >Int lengthBytes(BS)
rule #drop(N, BS:Bytes) => substrBytes(BS, N, lengthBytes(BS))
    requires lengthBytes(BS) >Int 0 andBool notBool N >Int lengthBytes(BS)

syntax Int ::= Bytes "[" Int "]" [function]
rule (B : BS) [ 0 ] => B
rule (_ : BS) [ I ] => BS [ I -Int 1] requires I >Int 0

syntax Int ::= "pow256" /* 2 ^Int 256 */
rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936 [macro]
```

We will try to prove the following lemma:
```
rule #asWord( BUF ) => #asWord( #drop(1, BUF) ) requires BUF [ 0 ] ==Int 0
```

We will use the following transitions:
```
start(BUF, X) => end(X) if BUF == nilBytes
start(BUF, X) => end(X) if exists B exists BS . BUF == B:BS
```

The backend evaluates it like this:
```
start(BUF, #asWord(BUF)) and BUF[ 0 ] ==Int 0
  = start(BUF, chop(Bytes2Int(BUF, BE, Unsigned))) and BUF[ 0 ] ==Int 0
  = start(BUF, Bytes2Int(BUF, BE, Unsigned) modInt pow256) and BUF[ 0 ] ==Int 0
  => end(Bytes2Int(BUF, BE, Unsigned) modInt pow256) and BUF[ 0 ] ==Int 0
       and BUF = nilBytes
   | end(Bytes2Int(BUF, BE, Unsigned) modInt pow256) and BUF[ 0 ] ==Int 0
       and exists B . exists BS . BUF = B : BS

end(chop(Bytes2Int(WS, BE, Unsigned))) and BUF[ 0 ] ==Int 0 and BUF = nilBytes
  = end(Bytes2Int(nilBytes, BE, Unsigned) modInt pow256)
        and nilBytes[ 0 ] ==Int 0 and BUF = nilBytes
  = end(0 modInt pow256) and bottom and BUF = nilBytes
  = bottom

end(Bytes2Int(BUF, BE, Unsigned) modInt pow256) and BUF[ 0 ] ==Int 0
        and exists B . exists BS . BUF = B : BS
  = end(Bytes2Int(BUF, BE, Unsigned) modInt pow256)
        and BUF[ 0 ] ==Int 0 and BUF = B : BS
  = end(Bytes2Int(B : BS, BE, Unsigned) modInt pow256)
        and (B:BS)[ 0 ] ==Int 0 and BUF = B : BS
  = end(Bytes2Int(B : BS, BE, Unsigned) modInt pow256)
        and B ==Int 0 and BUF = B : BS
  = end((B *Int (256 ^ length(BS)) + Bytes2Int(BS, BE, Unsigned)) modInt pow256)
        and B ==Int 0 and BUF = B : BS
```
and the SMT solver should be able to finish this.

