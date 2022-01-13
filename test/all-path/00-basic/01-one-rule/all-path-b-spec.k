requires "path.k"

module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-B-SPEC
  imports VERIFICATION
  
  // This should be provable as there is only one axiom.
  claim <k> a => b </k> [all-path]

endmodule
