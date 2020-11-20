module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-C-SPEC
  imports VERIFICATION
  imports PATH

  // This should not be provable as the only axiom is a => b.
  claim <k> a => c </k> [all-path]

endmodule
