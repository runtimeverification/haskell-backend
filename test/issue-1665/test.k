module TEST-SYNTAX
  imports INT

  syntax Pgm ::= "begin" Int | "end" Int
  syntax Int ::= fun(Int) [function, no-evaluators]
  syntax Bool ::= isFun(Int) [function, total, no-evaluators]

endmodule

module TEST
  imports TEST-SYNTAX

  configuration <k> $PGM:Pgm </k>

  rule begin X => end fun(X)

  rule [ceil-fun]: #Ceil(fun(X:Int)) => #Top requires isFun(X) [simplification]

endmodule
