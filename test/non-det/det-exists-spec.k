module VERIFICATION
  import TEST
endmodule

module DET-EXISTS-SPEC [all-path]
  import VERIFICATION
  // claim: Det rewrites to some Bool
  rule Det => ?X:Bool
endmodule