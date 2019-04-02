// This should be provable as transiting to b suffices
module ALL-PATH-B-OR-C-SPEC
  import PATH
  rule 
    <k> a => b #Or c </k>
  [claim, all-path]
endmodule
