module VERIFICATION
  imports IMP

  syntax StepSort ::= Int | Map
  syntax KItem ::= runTest (StepSort)
                 | doneTest (StepSort)

  rule runTest ( T ) => doneTest ( T )

endmodule

module WARN-BTM-HOOKS-SPEC
  imports VERIFICATION
  imports IMP

  rule <k> runTest ( Rho[3] ) => doneTest(X) </k>
    requires Rho ==K (1 |-> 2)

endmodule
