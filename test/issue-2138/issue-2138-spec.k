requires "test.k"

module ISSUE-2138-SPEC
  imports TEST

  claim
    <k> #assert i ( 1 , 0 ) ==Int 0 => .K </k>
      requires true #And ( #Forall X. { i ( X, 0 ) #Equals 0 } )

endmodule