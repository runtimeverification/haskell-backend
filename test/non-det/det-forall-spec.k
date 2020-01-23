module VERIFICATION
  import TEST
endmodule

module DET-FORALL-SPEC [all-path]
  import VERIFICATION
  // claim: Det rewrites to all Bool
  rule Det =>  X:Bool  [no-warning-i-know-what-i-am-doing-here]
endmodule
