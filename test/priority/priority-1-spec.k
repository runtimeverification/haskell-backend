requires "priority.k"

module PRIORITY-1-SPEC
    imports PRIORITY

    // This claim should not be provable.
    claim <k> runTest ( func4(X:Int) ) => doneTest ( seven ) ... </k>

endmodule
