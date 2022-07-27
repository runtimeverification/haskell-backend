module TEST-SYNTAX
  import INT

  syntax Pgm ::= "begin" Int | "end" Int
  syntax Int ::= fun(Int) [function, no-evaluators]
  syntax Bool ::= isFun(Int) [function, functional, no-evaluators]

endmodule

module TEST
  import TEST-SYNTAX

  configuration <k> $PGM:Pgm </k>

  rule begin X => end fun(X)

  rule [ceil-fun]: #Ceil(fun(X:Int)) => #True requires isFun(X) [simplification]

endmodule
