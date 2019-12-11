module VERIFICATION
  imports TEST-K-EQUAL
endmodule

module ISZERO-EQ-SPEC
  imports VERIFICATION

  rule <k> #iszero(I) => #done(1) </k> requires I ==Int 0
endmodule
