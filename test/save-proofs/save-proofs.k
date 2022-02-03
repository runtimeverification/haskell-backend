module SAVE-PROOFS

  imports INT

  syntax KItem ::= "AA" "(" Int ")"
  syntax KItem ::= "BB" "(" Int ")"
  syntax KItem ::= "CC" "(" Int ")"
  syntax KItem ::= "DD" "(" Int ")"

  // for test-1-spec
  rule BB(X:Int) => CC(X:Int)

  //for test-2-spec
  rule AA(X:Int) => BB(X:Int)
  rule CC(X:Int) => DD(X:Int)

endmodule
