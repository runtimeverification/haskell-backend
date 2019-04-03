module DISTINCT-SPEC
  imports PATH

  // should not be provable, as there is no axiom
  rule <k> a => b </k>
  [claim, all-path]
endmodule
