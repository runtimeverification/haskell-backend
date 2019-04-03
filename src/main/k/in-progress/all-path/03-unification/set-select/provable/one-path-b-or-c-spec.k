module ONE-PATH-B-OR-C-SPEC
  import PATH
  rule 
    <k> select => b #Or c </k>
    <state> SetItem(a) SetItem(b) SetItem(c) </state>
  [claim, one-path]
endmodule
