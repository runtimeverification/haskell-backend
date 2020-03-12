module RUN
  imports BOOL
  imports MAP

  syntax A ::= "a"
  syntax B ::= "b"
  syntax AB ::= A | B

  syntax Pgm ::= "begin" AB

  configuration <k> $PGM:Pgm </k>

  syntax AB ::= #lookup(AB, Map) [function]
  rule #lookup(KEY:AB, KEY |-> VAL _) => VAL

  rule <k> begin KEY => #lookup(KEY, a |-> a b |-> b) ... </k>

endmodule
