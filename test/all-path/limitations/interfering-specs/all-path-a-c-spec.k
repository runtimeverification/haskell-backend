requires "path.k"

module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-A-C-SPEC
  imports VERIFICATION

  // This should be provable
  claim <k> a => c </k> [all-path]

endmodule
