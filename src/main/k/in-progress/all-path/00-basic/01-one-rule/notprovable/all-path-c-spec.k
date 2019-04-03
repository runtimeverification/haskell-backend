// This should not be provable as the only axiom is a => b.
module ALL-PATH-C-SPEC
  import PATH
  rule 
    <k> a => c </k>
  [claim, all-path]
endmodule
