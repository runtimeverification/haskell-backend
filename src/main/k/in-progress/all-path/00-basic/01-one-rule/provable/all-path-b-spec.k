// This should be provable as there is only one axiom.
module ALL-PATH-B-SPEC
  imports PATH
  rule 
    <k> a => b </k>
  [claim, all-path]
endmodule
