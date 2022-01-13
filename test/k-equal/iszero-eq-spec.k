requires "test-k-equal.k"

module VERIFICATION
  imports TEST-K-EQUAL
endmodule

module ISZERO-EQ-SPEC
  imports VERIFICATION

  claim <k> #iszero(I) => #done(1) </k> requires I ==Int 0
endmodule
