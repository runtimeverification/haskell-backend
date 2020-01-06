// Two claims, the first one should fail, but is loaded from the saved claims
// for first.k, which allows the entire spec to pass.
module VERIFICATION
  imports SAVE-PROOFS

  rule AA(X:Int) => BB(X:Int)
  rule CC(X:Int) => DD(X:Int)
endmodule

module TEST-2-SPEC
  imports VERIFICATION

  rule BB(X:Int) => CC(X:Int)
  rule AA(X:Int) => DD(X:Int)
endmodule
