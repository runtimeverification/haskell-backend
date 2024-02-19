module TEST-SYNTAX
  imports INT
  imports BOOL
  imports ML-SYNTAX

  syntax Pgm ::= "begin" | "end"
  syntax Int ::= fun(Int) [function, no-evaluators]
  syntax Bool ::= isFun(Int) [function, total, no-evaluators]

endmodule

module TEST
  imports TEST-SYNTAX

  configuration <k> $PGM:Pgm </k>

  rule begin => end

  rule [ceil-fun]: #Ceil(fun(X:Int)) => #Top requires isFun(X) [simplification]

endmodule
