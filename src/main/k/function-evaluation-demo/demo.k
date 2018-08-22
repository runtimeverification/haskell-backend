module TRUTH
  syntax Truth
    ::= "TRUE"  [klabel(TRUE)]
      | "FALSE" [klabel(FALSE)]
endmodule

module PEANO
  imports TRUTH
  syntax Nat
    ::= "Zero" [klabel(Zero)]
      | Succ(Nat)
      | plus(Nat, Nat)      [function, functional]
      | times(Nat, Nat)     [function, functional]
      | minus(Nat, Nat)     [function, functional]

  rule plus(Zero, X:Nat) => X
  rule plus(Succ(X:Nat), Y:Nat) => Succ(plus(X, Y))

  rule times(Zero, _) => Zero
  rule times(Succ(X:Nat), Y:Nat) => plus(Y, times(X, Y))

  rule minus(Zero, _) => Zero
  rule minus(X:Nat, Zero) => X
  rule minus(Succ(X:Nat), Succ(Y:Nat)) => minus(X, Y)

  syntax Nat ::= factorial(Nat) [function, functional]
  rule factorial(Zero) => Succ(Zero)
  rule factorial(Succ(X:Nat)) => times(Succ(X:Nat), factorial(X))

  syntax Nat
    ::= fibonacci(Nat)               [function, functional]
      | fibonacciHelp(Nat, Nat, Nat) [function, functional]
  rule fibonacci(Zero) => Zero
  rule fibonacci(Succ(N:Nat)) => fibonacciHelp(N, Zero, Succ(Zero))
  rule fibonacciHelp(Zero, _, F:Nat) => F
  rule fibonacciHelp(Succ(N:Nat), F:Nat, F':Nat)
    => fibonacciHelp(N, F', plus(F, F'))

  syntax Truth ::= isZero(Nat) [function, functional]
  rule isZero(Zero) => TRUE
  rule isZero(Succ(_)) => FALSE

  syntax Truth ::= leq(Nat, Nat) [function, functional]
  rule leq(X:Nat, Y:Nat) => isZero(minus(X, Y))

  syntax Nat
    ::= mod(Nat, Nat) [function, functional]
      | modHelp(Nat, Nat, Nat) [function, functional]
  rule mod(X:Nat, Y:Nat) => modHelp(X, Y, Y)

  rule modHelp(Zero, Zero, Y:Nat) => Zero
  rule modHelp(Zero, Succ(NegRemainder:Nat), Succ(Y:Nat))
    => minus(Y, NegRemainder)
  rule modHelp(Succ(X:Nat), Zero, Y:Nat) => modHelp(Succ(X), Y, Y)
  rule modHelp(Succ(X:Nat), Succ(Y':Nat), Y:Nat) => modHelp(X, Y', Y)

  syntax Truth ::= divides(Nat, Nat) [function, functional]
  rule divides(D:Nat, N:Nat) => isZero(mod(N, D))
endmodule

module NAT-LIST
  imports PEANO
  syntax NatList
    ::= "Nil" [klabel(Nil)]
      | Cons(Nat, NatList)

  syntax Truth ::= null(NatList)  [function, functional]
  rule null(Nil) => TRUE
  rule null(Cons(_, _)) => FALSE

  syntax NatList ::= generate(Nat, Nat) [function, functional]
  rule generate(_, Zero) => Nil
  rule generate(Start:Nat, Succ(Count:Nat))
    => Cons(Start, generate(Succ(Start), Count))

  syntax NatList
    ::= sieveBy(Nat, NatList) [function, functional]
      | sieveByHelp(Nat, Truth, Nat, NatList) [function, functional]
  rule sieveBy(_, Nil) => Nil
  rule sieveBy(X:Nat, Cons(H:Nat, T:NatList))
    => sieveByHelp(X, divides(X, H), H, T)
  rule sieveByHelp(X:Nat, TRUE, H:Nat, T:NatList) => sieveBy(X, T)
  rule sieveByHelp(X:Nat, FALSE, H:Nat, T:NatList)
    => Cons(H, sieveBy(X, T))

  syntax NatList ::= sieve(NatList) [function, functional]
  rule sieve(Nil) => Nil
  rule sieve(Cons(H:Nat, T:NatList)) => Cons(H, sieve(sieveBy(H, T)))

  syntax NatList ::= primesUpTo(Nat) [function, functional]
  rule primesUpTo(Zero) => Nil
  rule primesUpTo(Succ(Zero)) => Nil
  rule primesUpTo(Succ(Succ(N:Nat)))
    => sieve(generate(Succ(Succ(Zero)), Succ(N)))
endmodule

module DEMO
  imports NAT-LIST
endmodule