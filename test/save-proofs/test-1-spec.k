module VERIFICATION
  imports SAVE-PROOFS

  rule BB(X:Int) => CC(X:Int)
endmodule

// This claim is proven and saved.
module TEST-1-SPEC
  imports VERIFICATION

  rule BB(X:Int) => CC(X:Int)
endmodule
