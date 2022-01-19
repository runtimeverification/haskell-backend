requires "test.k"

module VERIFICATION
  imports TEST
endmodule

module ISSUE-1916-SPEC
  imports VERIFICATION

  // Proving this claim requires that the right-hand side is simplified using
  // the conditions from the left-hand side.
  //
  claim <k> begin => end </k> requires isFun(X) ensures true #And #Ceil(fun(X))
endmodule
