module VERIFICATION
  import TEST
endmodule

module ISSUE-2138-SPEC
  import VERIFICATION

  claim
    <k> #assert i ( 1 , 0 ) ==Int 0 => . </k>
      requires true #And ( #Forall X. { i ( X, 0 ) #Equals 0 } )

endmodule