module VERIFICATION
  imports TEST

  syntax StepSort ::= Set
  syntax    KItem ::= runTest  ( StepSort )
                    | doneTest ( StepSort )
 // ------------------------------------------
  rule runTest( T ) => doneTest( T )

endmodule

module TEST-2-SPEC
  imports VERIFICATION

  claim <k> runTest( f( SetItem(X:Element) SetItem(Y:Element) ) ) </k>
    => <k> doneTest( SetItem(g(X)) SetItem(g(Y)) ) </k>
    requires
      (X =/=K Y)
      andBool (g(X) =/=K g(Y))

endmodule
