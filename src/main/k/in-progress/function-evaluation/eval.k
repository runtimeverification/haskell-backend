module PEANO
  imports DOMAINS

  syntax Nat ::= "Zero"    [klabel(Zero)]
               | Succ(Nat)

// safe function
  syntax Bool ::= isZero(Nat) [function]
  rule isZero(Zero) => true
  rule isZero(Succ(_)) => false

// safe function
  syntax Bool ::= isOne(Nat) [function]
  rule isOne(Zero) => false
  rule isOne(Succ(N)) => isZero(N)

// acceptable function
  syntax Nat ::= plus(Nat, Nat) [function]
  rule plus(Zero, X) => X
  rule plus(Succ(X), Y) => Succ(plus(X, Y))

// safe, but partial function
  syntax Nat ::= Pred(Nat) [function]
  rule Pred(Succ(N)) => N

  syntax Nat ::= "symNat" [function]
  rule symNat => ?N:Nat

endmodule

module NAT-LIST
  imports DOMAINS
  imports PEANO
  syntax NatList ::= "Nil" [klabel(Nil)]
                   | Cons(Nat, NatList)

// acceptable function
  syntax Nat ::= lenNat(NatList)  [function]
  rule lenNat(Nil) => Zero
  rule lenNat(Cons(_, T)) => Succ(lenNat(T))

// complicated function
  syntax Int ::= lenInt(NatList) [function]
  rule lenInt(Nil) => 0
  rule lenInt(Cons(_, T)) => 1 +Int lenInt(T)

  syntax NatList ::= "symNatList" [function]
  rule symNatList => ?LS:NatList

endmodule

module INTEGER
  imports DOMAINS

// safe function
  syntax Int ::= succ(Int) [function]
  rule succ(X) => X +Int 1

  syntax Int ::= "symInt" [function]
  rule symInt => ?I:Int

endmodule

module EVAL
  imports PEANO
  imports NAT-LIST
  imports INTEGER
endmodule
