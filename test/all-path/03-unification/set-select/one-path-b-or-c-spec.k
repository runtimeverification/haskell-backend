requires "path.k"

module ONE-PATH-B-OR-C-SPEC
  imports PATH

  claim <k> select => b #Or c </k>
       <state> SetItem(b) SetItem(c) </state>
    [one-path]

endmodule
