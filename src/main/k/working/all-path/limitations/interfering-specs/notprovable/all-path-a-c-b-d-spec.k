// This should be provable. However, since the algorithm gives precedence
// to applying claims, it would not succeed in proving this.
//
// This seems like a reasonable limitation; However, it should be well
// documented and shown as an examples in tutorials for beginners.
module ALL-PATH-A-C-B-D-SPEC
  imports PATH
  rule 
    <k> a => c </k>
  [claim, all-path]
  rule 
    <k> b => d </k>
  [claim, all-path]
endmodule
