requires "path.k"

module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-B-D-SPEC
  imports VERIFICATION

  // This should be provable
  claim <k> b => d </k> [all-path]

endmodule
