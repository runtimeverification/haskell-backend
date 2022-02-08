requires "path.k"

module ALL-PATH-F-SPEC
  imports PATH
  imports PATH

  // This should be provable as both one-path and all-path.
  claim <k> a => f </k> [all-path]
endmodule
