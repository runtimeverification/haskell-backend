// This should be provable as both one-path and all-path.
module ALL-PATH-F-SPEC
  import PATH
  rule 
    <k> a => f </k>
  [claim, all-path]
endmodule
