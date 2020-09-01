module VERIFICATION
  imports PATH

endmodule

module ONE-PATH-B-OR-C-SPEC
  imports VERIFICATION
  imports PATH

  rule <k> select => b #Or c </k>
       <state> SetItem(b) SetItem(c) </state>
    [one-path]

endmodule
