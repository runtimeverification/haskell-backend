module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-F-SPEC
  imports VERIFICATION
  imports PATH

  // This should be provable as both one-path and all-path.
  claim <k> a => f </k> [all-path]
endmodule
