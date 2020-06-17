module TEST
  imports INT
  imports MAP

  syntax Prog ::= "a" "(" Map ")"
                | "b" "(" Int ")"
                | "c" "(" Int ")"

  rule b(X) => c(5 /Int 0)

endmodule
