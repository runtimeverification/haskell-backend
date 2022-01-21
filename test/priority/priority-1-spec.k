requires "priority.k"

module VERIFICATION
    imports PRIORITY

    syntax KItem ::= runTest  ( S )
                   | doneTest ( S )

    rule runTest ( T ) => doneTest ( T )

endmodule

module PRIORITY-1-SPEC
    imports VERIFICATION

    // This claim should not be provable.
    claim <k> runTest ( func4(X:Int) ) => doneTest ( seven ) ... </k>

endmodule
