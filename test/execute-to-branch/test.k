module TEST
  imports BOOL

  syntax Foo ::= "a" | "b" | "c" | "d" | "e"

  rule a => b
  rule b => c
  rule c => d
  rule c => e
endmodule
