module VERIFICATION
  import TEST
endmodule

module NON-DET-FORALL-SPEC [all-path]
  import VERIFICATION
  // claim: NonDet rewrites to all Bool
  rule NonDet =>  X:Bool  [no-warning-i-know-what-i-am-doing-here]
endmodule