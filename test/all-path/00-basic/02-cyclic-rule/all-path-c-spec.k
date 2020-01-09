module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-C-SPEC
  imports VERIFICATION
  imports PATH

  // Everything is provable if I can reach a cycling rule
  rule <k> a => c </k> [all-path]

endmodule
