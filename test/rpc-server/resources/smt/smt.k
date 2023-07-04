module TEST
  imports INT

  syntax Int ::= "pow256"               [alias] /* 2 ^Int 256 */

  rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936

  syntax Int ::= chop ( Int ) [function, total, smtlib(chop)]

  rule [modRule]: chop(I:Int) => I modInt pow256 [concrete, smt-lemma]

  rule [idemRule]: chop(chop(I)) => chop(I)      [simplification, smt-lemma]

endmodule
