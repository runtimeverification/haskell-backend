// This should be provable. However, since the algorithm gives precedence
// to applying claims, it would not succeed in proving this.
//
// This seems like a reasonable limitation; However, it should be well
// documented and shown as an examples in tutorials for beginners.

requires "path.k"

module ALL-PATH-A-C-B-D-SPEC
  imports PATH

  claim <k> a => c </k> [all-path]
  claim <k> b => d </k> [all-path]

endmodule
