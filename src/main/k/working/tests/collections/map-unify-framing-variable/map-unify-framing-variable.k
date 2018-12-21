module MAP-UNIFY-FRAMING-VARIABLE

  imports DOMAINS

  syntax Val ::= "a" | "b" | "c"

  configuration
    <T>
      <k> $PGM:Val </k>
      <s1> a |-> 1 b |-> 2 c |-> 3 </s1>
    </T>

  rule
    <k> V:Val </k>
    <s1> ((V |-> _) => .Map) Rho:Map </s1>

endmodule
