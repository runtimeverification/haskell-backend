requires "path.k"

module ALL-PATH-B-SPEC
  imports PATH

  // Everything is provable if I can reach a cycling rule
  claim <k> a => b </k> [all-path]

endmodule
