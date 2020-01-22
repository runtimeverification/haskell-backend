module DEMO

  imports BOOL

  syntax S ::= "a" | "b" | f(S) [function]
  rule f(a) => b
  rule f(_) => a [owise]
endmodule