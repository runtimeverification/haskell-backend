// Two claims, the first one should fail, but is loaded from the saved claims
// for first.k, which allows the entire spec to pass.
module VERIFICATION
  imports SAVE-PROOFS

  rule AA(X:Int) => BB(X:Int)
  rule CC(X:Int) => DD(X:Int)
endmodule

module TEST-2-SPEC
  imports VERIFICATION

  // This claim would fail, but it is loaded from the saved claims.
  claim BB(X:Int) => CC(X:Int)
  // This claim requires the first claim.
  claim AA(X:Int) => DD(X:Int)
endmodule
