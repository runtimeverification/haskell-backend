module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-B-OR-C-SPEC
  imports VERIFICATION
  imports PATH

  rule <k> select => b #Or c </k>
       <state> SetItem(b) SetItem(c) </state>
    [all-path]

endmodule
