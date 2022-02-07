// Two claims, the first one should fail, but is loaded from the saved claims
// for first.k, which allows the entire spec to pass.

require "save-proofs.k"

module TEST-2-SPEC
  imports SAVE-PROOFS

  // This claim would fail, but it is loaded from the saved claims.
  claim BB(X:Int) => CC(X:Int)
  // This claim requires the first claim.
  claim AA(X:Int) => DD(X:Int)
endmodule
