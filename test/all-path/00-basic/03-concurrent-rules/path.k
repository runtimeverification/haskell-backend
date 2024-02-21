module PATH
  imports BOOL
  imports INT
  syntax S ::= "a" | "b" | "c"

  rule a => b
  rule a => c
endmodule
