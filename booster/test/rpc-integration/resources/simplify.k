module SIMPLIFY
  imports INT
  imports ID-SYNTAX
  imports K-EQUAL

  syntax Int ::= f ( Int ) [function, no-evaluators] // a non-concrete value

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
