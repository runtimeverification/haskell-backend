module TEST
  imports BOOL
  imports BYTES
  imports INT

  syntax A ::= a(Int, Bool) | "b"
  rule a(I, _) => b requires I <=Int 0
  rule a(I, _) => b requires notBool (I <=Int 0)

  syntax Bool ::= f(Int)  [function, total]
  rule f(0) => true
  rule f(I) => loop(I) requires I =/=Int 0

  syntax Bool ::= g(Int)  [function]

  // this simplification shooed never be applied, as it requires false.
  // However, it will be applied if we simplify the configuration assuming
  // the remainder predicate derived from the side conditions of the rules
  // for a(_,_). Not every #Bottom is the same, since some are diverging!
  rule g(_I) => true requires false [simplification]

  rule f(I) => f(I) requires g(I)  [simplification]

  syntax Bool ::= loop(Int)  [function]
  syntax Bool ::= loop1(Int)  [function]
  syntax Bool ::= loop2(Int)  [function]
  rule loop(I) => loop1(I) requires g(I)  [simplification]
  rule loop1(I) => loop2(I) [simplification]
  rule loop2(I) => loop1(I) [simplification]

endmodule
