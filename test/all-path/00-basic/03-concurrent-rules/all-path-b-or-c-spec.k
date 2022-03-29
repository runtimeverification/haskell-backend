requires "path.k"

module ALL-PATH-B-OR-C-SPEC
  imports PATH

// This should be provable as both one-path and all-path.
  claim <k> a => b #Or c </k> [all-path]

endmodule
