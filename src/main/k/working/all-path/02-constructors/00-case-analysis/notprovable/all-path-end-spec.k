// This should not be provable both one-path and all-path.
// because it does not hold for X = c
module ALL-PATH-END-SPEC
  import PATH
  rule 
    <k> g(X:S) => end </k>
  [claim, all-path]
endmodule
