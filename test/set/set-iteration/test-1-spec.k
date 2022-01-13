requires "test.k"

module VERIFICATION
  imports TEST

  syntax StepSort ::= Set
  syntax    KItem ::= runTest  ( StepSort )
                    | doneTest ( StepSort )
 // ------------------------------------------
  rule runTest( T ) => doneTest( T )

endmodule

module TEST-1-SPEC
  imports VERIFICATION

  claim <k> runTest( f( SetItem(a) SetItem(b) ) ) </k>
    => <k> doneTest( SetItem(b) SetItem(c) ) </k>

endmodule
