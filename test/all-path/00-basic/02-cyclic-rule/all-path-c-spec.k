requires "path.k"

module ALL-PATH-C-SPEC
  imports PATH

  // Everything is provable if I can reach a cycling rule
  claim <k> a => c </k> [all-path]

endmodule
