module TINY
  imports DOMAINS-SYNTAX
  imports DOMAINS

  syntax S ::= "a" | "b" | "c"

  rule a => b [label(mylabel)]

endmodule
