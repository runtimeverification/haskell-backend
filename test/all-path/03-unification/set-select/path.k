module PATH
  imports BOOL
  imports INT
  imports SET
  syntax S ::= "a" | "b" | "c" 
  syntax Cmd ::= "select"

  configuration <k> .K </k> <state> .Set </state>

  rule <k> select => X ...</k> <state>... SetItem(X:S) ...</state>
endmodule
