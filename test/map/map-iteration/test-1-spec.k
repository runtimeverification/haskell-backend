requires "test.k"

module VERIFICATION
  imports TEST

  syntax StepSort ::= Map
  syntax    KItem ::= runTest  ( StepSort )
                    | doneTest ( StepSort )
 // ------------------------------------------
  rule runTest( T ) => doneTest( T )

endmodule

module TEST-1-SPEC
  imports VERIFICATION

  claim <k> runTest( f( a |-> 1 b |-> 2 ) ) </k> => <k> doneTest( b |-> 2 c |-> 3 ) </k>

endmodule

