module VERIFICATION
  import TEST
endmodule

module NON-DET-EXISTS-SPEC [all-path]
  import VERIFICATION
  // claim: NonDet rewrites to some bool
  rule NonDet => ?X:Bool
endmodule
