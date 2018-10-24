module LIST-UNIFY-1
  
  imports DOMAINS
  
  syntax Val ::= "a" | "b" | "c"

  configuration
    <T>
      <k> $PGM:Val </k>
      <s1> ListItem(a) ListItem(b) ListItem(c) </s1>
    </T>

  rule 
    <k> V:Val </k>
    <s1> (ListItem(V) => .List) X:List </s1>

endmodule