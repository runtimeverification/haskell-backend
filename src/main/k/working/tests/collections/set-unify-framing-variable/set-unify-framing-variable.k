module SET-UNIFY-FRAMING-VARIABLE

  imports BOOL
  imports SET

  syntax Val ::= "a" | "b" | "c"

  configuration
    <T>
      <k> $PGM:Val </k>
      <s1> SetItem(a) SetItem(b) SetItem(c) </s1>
    </T>

  rule
    <k> V:Val </k>
    <s1> (SetItem(V) => .Set) X:Set </s1>
    requires notBool (V in X)
endmodule
