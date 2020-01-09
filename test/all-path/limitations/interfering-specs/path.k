module PATH
  import BOOL
  syntax S ::= "a" | "b" | "c" | "d"

  rule a => b
  rule b => c
  rule c => d
endmodule
