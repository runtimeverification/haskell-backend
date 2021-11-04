requires "path.k"

module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-SELECT-A-B-C-SPEC
  imports VERIFICATION
  imports PATH

  // This should be provable as an one-path claim, but should not be provable as an
  //all-path claim.
  claim <k> select => b #Or c </k>
       <state> SetItem(a) SetItem(b) SetItem(c) </state> [all-path]

endmodule
