requires "test.k"

module TEST-1-SPEC
  imports TEST

  claim <k> runTest( f( a |-> 1 b |-> 2 ) ) </k> => <k> doneTest( b |-> 2 c |-> 3 ) </k>

endmodule

