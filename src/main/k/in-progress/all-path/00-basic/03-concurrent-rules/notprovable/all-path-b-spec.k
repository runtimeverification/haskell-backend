// This should be provable as an one-path claim, but should not be provable as an 
//all-path claim.
module ALL-PATH-B-SPEC
  import PATH
  rule 
    <k> a => b </k>
  [claim, all-path]
endmodule
