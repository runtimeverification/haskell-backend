requires "path.k"

module ALL-PATH-B-OR-C-SPEC
  imports PATH

  claim <k> select => b #Or c </k>
       <state> SetItem(b) SetItem(c) </state>
    [all-path]

endmodule
