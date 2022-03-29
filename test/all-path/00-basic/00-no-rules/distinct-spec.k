requires "path.k"

module DISTINCT-SPEC
  imports PATH

  // should not be provable, as there is no axiom
  claim <k> a => b </k> [all-path]

endmodule
