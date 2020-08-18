module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-B-OR-C-SPEC
  imports VERIFICATION
  imports PATH

  rule <k> select => ?X </k>
       <state> SetItem(b) SetItem(c) </state> 
    ensures ?X ==K b orBool ?X ==K c [all-path]

endmodule
