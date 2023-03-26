module BB
  imports BOOL
endmodule

/*
## Booleans section of domains.md (imported above) at the time of writing:
--------------------------------------------------------------------------

Booleans
--------

Provided here is the syntax of an implementation of boolean algebra in K.
This type is hooked to an implementation of booleans provided by the backend.
Note that this algebra is different from the builtin truth in matching logic.
You can, however, convert from the truth of the `Bool` sort to the truth in
matching logic via the expression `{B #Equals true}`.

The boolean values are `true` and `false`.

```k
module SORT-BOOL
  syntax Bool [hook(BOOL.Bool)]
endmodule

module BOOL-SYNTAX
  imports SORT-BOOL
  syntax Bool ::= "true"  [token]
  syntax Bool ::= "false" [token]
endmodule

module BOOL-COMMON
  imports private BASIC-K
  imports BOOL-SYNTAX
```

### Basic boolean arithmetic

You can:

* Negate a boolean value.
* AND two boolean values.
* XOR two boolean values.
* OR two boolean values.
* IMPLIES two boolean values (i.e., `P impliesBool Q` is the same as
  `notBool P orBool Q`)
* Check equality of two boolean values.
* Check inequality of two boolean values.

Note that only `andThenBool` and `orElseBool` are short-circuiting. `andBool`
and `orBool` may be short-circuited in concrete backends, but in symbolic
ackends, both arguments will be evaluated.

```k
  syntax Bool ::= "notBool" Bool          [function, total, klabel(notBool_), symbol, smt-hook(not), boolOperation, latex(\neg_{\scriptstyle\it Bool}{#1}), hook(BOOL.not)]
                > Bool "andBool" Bool     [function, total, klabel(_andBool_), symbol, left, smt-hook(and), boolOperation, latex({#1}\wedge_{\scriptstyle\it Bool}{#2}), hook(BOOL.and)]
                | Bool "andThenBool" Bool [function, total, klabel(_andThenBool_), symbol, left, smt-hook(and), boolOperation, hook(BOOL.andThen)]
                | Bool "xorBool" Bool     [function, total, klabel(_xorBool_), symbol, left, smt-hook(xor), boolOperation, hook(BOOL.xor)]
                | Bool "orBool" Bool      [function, total, klabel(_orBool_), symbol, left, smt-hook(or), boolOperation, latex({#1}\vee_{\scriptstyle\it Bool}{#2}), hook(BOOL.or)]
                | Bool "orElseBool" Bool  [function, total, klabel(_orElseBool_), symbol, left, smt-hook(or), boolOperation, hook(BOOL.orElse)]
                | Bool "impliesBool" Bool [function, total, klabel(_impliesBool_), symbol, left, smt-hook(=>), boolOperation, hook(BOOL.implies)]
                > left:
                  Bool "==Bool" Bool      [function, total, klabel(_==Bool_), symbol, left, smt-hook(=), hook(BOOL.eq)]
                | Bool "=/=Bool" Bool     [function, total, klabel(_=/=Bool_), symbol, left, smt-hook(distinct), hook(BOOL.ne)]
```

### Implementation of Booleans

The remainder of this section consists of an implementation in K of the
operations listed above.

```k
  rule notBool true => false
  rule notBool false => true

  rule true andBool B:Bool => B:Bool
  rule B:Bool andBool true => B:Bool
  rule false andBool _:Bool => false
  rule _:Bool andBool false => false

  rule true andThenBool K::Bool => K
  rule K::Bool andThenBool true => K
  rule false andThenBool _ => false
  rule _ andThenBool false => false

  rule false xorBool B:Bool => B:Bool
  rule B:Bool xorBool false => B:Bool
  rule B:Bool xorBool B:Bool => false

  rule true orBool _:Bool => true
  rule _:Bool orBool true => true
  rule false orBool B:Bool => B
  rule B:Bool orBool false => B

  rule true orElseBool _ => true
  rule _ orElseBool true => true
  rule false orElseBool K::Bool => K
  rule K::Bool orElseBool false => K

  rule true impliesBool B:Bool => B
  rule false impliesBool _:Bool => true
  rule _:Bool impliesBool true => true
  rule B:Bool impliesBool false => notBool B

  rule B1:Bool =/=Bool B2:Bool => notBool (B1 ==Bool B2)
endmodule

module BOOL-KORE [kore, symbolic]
  imports BOOL-COMMON

  rule {true #Equals notBool @B} => {false #Equals @B} [simplification]
  rule {notBool @B #Equals true} => {@B #Equals false} [simplification]
  rule {false #Equals notBool @B} => {true #Equals @B} [simplification]
  rule {notBool @B #Equals false} => {@B #Equals true} [simplification]

  rule {true #Equals @B1 andBool @B2} => {true #Equals @B1} #And {true #Equals @B2} [simplification]
  rule {@B1 andBool @B2 #Equals true} => {@B1 #Equals true} #And {@B2 #Equals true} [simplification]
  rule {false #Equals @B1 orBool @B2} => {false #Equals @B1} #And {false #Equals @B2} [simplification]
  rule {@B1 orBool @B2 #Equals false} => {@B1 #Equals false} #And {@B2 #Equals false} [simplification]
endmodule

module BOOL
  imports BOOL-COMMON
  imports BOOL-KORE
endmodule
```
*/
