requires "path.k"

module ONE-PATH-B-SPEC
  imports PATH

  // This should be provable as an one-path claim, but should not be provable as an
  //all-path claim.
  claim <k> a => c </k> [one-path]

endmodule
