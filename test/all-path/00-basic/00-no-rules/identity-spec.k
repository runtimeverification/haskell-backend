requires "path.k"

module VERIFICATION
  imports PATH

endmodule

module IDENTITY-SPEC
  imports VERIFICATION

  claim <k> a => a </k> [all-path]

endmodule
