// This should be provable as an one-path claim, but should not be provable as an 
//all-path claim.
module ALL-PATH-B-OR-C-SPEC
  import PATH
  rule 
    <k> select => b #Or c </k>
    <state> SetItem(a) SetItem(b) SetItem(c) </state>
  [claim, all-path]
endmodule
