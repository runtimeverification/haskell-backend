// Two claims, one passes and is saved to a file, the other one fails.
module VERIFICATION
  imports SAVE-PROOFS

  rule BB(X:Int) => CC(X:Int)
endmodule

module TEST-1
  imports VERIFICATION

  rule BB(X:Int) => CC(X:Int)
  rule AA(X:Int) => DD(X:Int)
endmodule
