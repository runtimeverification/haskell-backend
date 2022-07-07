module TEST-SYNTAX
endmodule

module TEST
  imports DOMAINS

  configuration <k> $PGM:K </k> <state> .Map </state>
  syntax KItem ::= "foo" | "bar"

  rule <k> RuleVar => bar </k>
       <state>... RuleVar |-> 0 </state>
endmodule
