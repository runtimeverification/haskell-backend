module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-B-OR-C-SPEC
  import PATH

  // This should be provable as transiting to b suffices
  claim <k> a => b #Or c </k> [all-path]

endmodule
