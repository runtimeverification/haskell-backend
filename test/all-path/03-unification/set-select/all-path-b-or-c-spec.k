module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-B-OR-C-SPEC
  imports VERIFICATION
  imports PATH

  // TODO (#1278): ... => ?X ensures ?X ==K b orBool ?X ==K c
  rule <k> select => b #Or c </k>
       <state> SetItem(b) SetItem(c) </state>
    [all-path]

endmodule
