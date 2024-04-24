module SIMPLIFY
  imports INT
  imports BOOL
  imports ID-SYNTAX
  imports K-EQUAL

  syntax Int ::= f ( Int ) [function, no-evaluators] // a non-concrete value
               | g ( Int ) [function, klabel("g"), symbol] // for simplification purposes

  syntax Bool ::= p1 ( Int ) [function, total, no-evaluators, klabel("p1"), symbol]
                | p2 ( Int ) [function, total, no-evaluators, klabel("p2"), symbol]
                | p3 ( Int ) [function, total, klabel("p3"), symbol]

  // an indirect simplifiation loop
  rule [p1-if-p2]: p1(X) => true requires p2(X) [simplification]
  rule [p2-if-p1]: p2(X) => true requires p1(X) [simplification]
  // simplification of terms involving p1(_someInt) or p2(_someInt) will enter
  // a loop of p1, p2, p1, p2... until the maximum recursion depth is reached
  // and then bail out in booster. Simplification in kore-rpc _loops to infinity_.

  // a set of function equations that require recursive evaluation of side condition p3
  rule [eval-g]: g(X) => X requires p3(X)

  rule [p3-true]: p3(1) => true
  rule [p3-false]: p3(_) => false [owise]


/* Simplification rules from domains.md, reproduced here for documentation

  // Arithmetic Normalization
  rule I +Int 0 => I [simplification]
  rule I -Int 0 => I [simplification]

  rule X modInt N => X requires 0 <=Int X andBool X <Int N [simplification]
  rule X   %Int N => X requires 0 <=Int X andBool X <Int N [simplification]

  // Arithmetic Normalization
  rule I +Int B => B +Int I          [concrete(I), symbolic(B), simplification(51)]
  rule A -Int I => A +Int (0 -Int I) [concrete(I), symbolic(A), simplification(51)]

  rule (A +Int I2) +Int I3 => A +Int (I2 +Int I3) [concrete(I2, I3), symbolic(A), simplification]
  rule I1 +Int (B +Int I3) => B +Int (I1 +Int I3) [concrete(I1, I3), symbolic(B), simplification]
  rule I1 -Int (B +Int I3) => (I1 -Int I3) -Int B [concrete(I1, I3), symbolic(B), simplification]
  rule I1 +Int (I2 +Int C) => (I1 +Int I2) +Int C [concrete(I1, I2), symbolic(C), simplification]
  rule I1 +Int (I2 -Int C) => (I1 +Int I2) -Int C [concrete(I1, I2), symbolic(C), simplification]
  rule (I1 -Int B) +Int I3 => (I1 +Int I3) -Int B [concrete(I1, I3), symbolic(B), simplification]
  rule I1 -Int (I2 +Int C) => (I1 -Int I2) -Int C [concrete(I1, I2), symbolic(C), simplification]
  rule I1 -Int (I2 -Int C) => (I1 -Int I2) +Int C [concrete(I1, I2), symbolic(C), simplification]
  rule (C -Int I2) -Int I3 => C -Int (I2 +Int I3) [concrete(I2, I3), symbolic(C), simplification]

  rule I1 &Int (I2 &Int C) => (I1 &Int I2) &Int C [concrete(I1, I2), symbolic(C), simplification]
*/
endmodule
