requires "test.k"

module VERIFICATION
  import TEST
endmodule

module ISSUE-1665-SPEC
  import VERIFICATION

  // Proving this claim requires inferring that the left-hand side of an
  // intermediate proof goal is defined.
  //
  claim <k> begin _ => end ?_ </k>
endmodule
