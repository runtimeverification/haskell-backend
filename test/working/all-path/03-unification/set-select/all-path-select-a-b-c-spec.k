module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-SELECT-A-B-C-SPEC
  imports VERIFICATION
  imports PATH

  // This should be provable as an one-path claim, but should not be provable as an
  //all-path claim.
  rule <k> select => ?X </k>
       <state> SetItem(a) SetItem(b) SetItem(c) </state>
    ensures ?X ==K b orBool ?X ==K c [all-path]

endmodule
