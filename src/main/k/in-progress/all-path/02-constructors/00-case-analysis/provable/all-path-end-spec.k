// This should be provable as both one-path and all-path.
// Note that this uses that S is only formed of a | b | c
module ALL-PATH-END-SPEC
  import PATH
  rule 
    <k> f(X:S) => end </k>
  [claim, all-path]
endmodule
