requires "path.k"

module ALL-PATH-TOTAL-SPEC
  imports PATH

  // This should be provable as both one-path and all-path.
  // Note that this uses that S is only formed of a | b | c
  claim <k> total(X:S) => end </k> [all-path]

endmodule
