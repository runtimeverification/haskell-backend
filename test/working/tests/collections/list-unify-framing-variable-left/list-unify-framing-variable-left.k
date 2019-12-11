module LIST-UNIFY-FRAMING-VARIABLE-LEFT

  imports DOMAINS

  syntax Val ::= "a" | "b" | "c"

  configuration
    <T>
      <k> $PGM:Val </k>
      <s1> ListItem(a) ListItem(b) ListItem(c) </s1>
    </T>

  rule
    <k> V:Val </k>
    <s1> X:List (ListItem(V) => .List) </s1>

endmodule
