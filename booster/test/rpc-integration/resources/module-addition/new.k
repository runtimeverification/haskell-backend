requires "test.k"

module NEW
imports TEST

  // add two more states
  syntax State ::= "e" [token]
                 | "f" [token]

  rule [DE]: <k> d => e ... </k>
  rule [EF]: <k> e => f ... </k>

endmodule
