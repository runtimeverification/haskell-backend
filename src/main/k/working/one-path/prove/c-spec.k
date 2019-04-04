module VERIFICATION
  imports ABC
endmodule

module C-SPEC
  imports VERIFICATION

  rule <k> a => c </k>
  [claim]
endmodule
