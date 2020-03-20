module RUN
  imports BOOL
  imports INT
  imports MAP

  syntax A ::= "a"
  syntax B ::= "b"
  syntax AB ::= A | B

  syntax Pgm ::= "begin" AB

  configuration <k> $PGM:Pgm </k>

  syntax AB ::= #lookup(AB, Map) [function]

  rule #lookup(KEY1, KEY2 |-> VAL M) => #lookup(KEY1, M)
    requires notBool (KEY1 ==K KEY2)
  rule #lookup(KEY, KEY |-> VAL _) => VAL

  rule <k> begin KEY => #lookup(KEY, a |-> a b |-> b) ... </k>

endmodule
