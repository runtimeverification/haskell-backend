requires "path.k"

module ALL-PATH-C-SPEC
  imports PATH

  // This should be provable as an one-path claim, but should not be provable as an
  //all-path claim.
  claim <k> select => c </k>
       <state> SetItem(b) SetItem(c) </state> [all-path]

endmodule
