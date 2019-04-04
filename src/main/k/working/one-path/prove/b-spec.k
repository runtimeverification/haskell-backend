module VERIFICATION
  imports ABC
endmodule

module B-SPEC
  imports VERIFICATION

  rule <k> a => b </k>
  [claim]
endmodule