// This should be provable as both one-path and all-path.
module ALL-PATH-B-OR-C-SPEC
  rule 
    <k> a => b #Or c </k>
  [claim, all-path]
endmodule
