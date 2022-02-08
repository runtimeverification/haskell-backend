requires "test-k-equal.k"

module ISZERO-GE-SPEC
  imports TEST-K-EQUAL

  claim <k> #iszero(I) => #done(1) </k> requires I >=Int 0
endmodule
