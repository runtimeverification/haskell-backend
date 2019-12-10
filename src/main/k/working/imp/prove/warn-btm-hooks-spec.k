requires "domains.k"

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
  imports MAP

  rule <k> runTest ( X ) => doneTest( Y ) </k>
    requires X ==K (.Map [3])

endmodule
