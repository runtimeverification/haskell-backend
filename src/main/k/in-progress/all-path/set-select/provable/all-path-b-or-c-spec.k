module ALL-PATH-B-OR-C-SPEC
  import PATH
  rule 
    <k> select => b #Or c </k>
    <state> SetItem(b) SetItem(c) </state>
  [claim, all-path]
endmodule
