module TINY
  imports DOMAINS-SYNTAX
  imports DOMAINS

  syntax S ::= "a" | "b" | "c"

  rule a => b [label(A2B)]

  rule b => c [label(B2C)]

endmodule
