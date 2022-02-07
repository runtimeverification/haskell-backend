requires "test.k"

module ISSUE-1665-SPEC
  import TEST

  // Proving this claim requires inferring that the left-hand side of an
  // intermediate proof goal is defined.
  //
  claim <k> begin _ => end ?_ </k>
endmodule
