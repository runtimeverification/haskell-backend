module SMT-LEMMA
  imports INT
  syntax KItem ::= delayed(KItem) [strict]
  syntax KResult ::= Int

  syntax Bool ::= test(Int) [smtlib(smt_test), function, total]

  syntax KItem ::= "symInt"

  rule delayed(X:Int) => test(X)

  rule symInt => ?X:Int

  rule test(X) => X >Int 5 [simplification, concrete, smt-lemma]
endmodule
