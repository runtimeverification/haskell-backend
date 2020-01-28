module PATH
  import DOMAINS
  syntax S ::= "a" | "b" | "c" | "d"

  rule a => b
  rule b => c
  rule c => d
endmodule
