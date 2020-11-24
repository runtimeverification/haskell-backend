module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-B-SPEC
  imports VERIFICATION
  imports PATH

  // Everything is provable if I can reach a cycling rule
  claim <k> a => b </k> [all-path]

endmodule
