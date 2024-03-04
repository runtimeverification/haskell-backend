module DOMAIN-VALUES

  imports INT

  syntax A ::= "a"
  syntax B ::= "b"
  syntax AB ::= A | B

  syntax Sub ::= "ctor" A [overload(ctor)]
  syntax Sub ::= Int

  syntax Sup ::= Sub
  syntax Sup ::= "ctor" AB [overload(ctor)]

  syntax Pgm ::= Sup
  syntax Pgm ::= "end"

  configuration <k> $PGM:Pgm </k>

  rule <k> ctor _:AB => end </k>
  rule <k> _:Int => end </k>

endmodule