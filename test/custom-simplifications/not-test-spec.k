module NOT-TEST-SPEC
    imports TEST

    claim <k> runTest( X ) => . </k>
        requires #Not ( { X +Int X +Int X #Equals X *Int 3 } )
    // should work  ^^^ try `DebugEquationApplication` (-> wiki https://github.com/runtimeverification/haskell-backend/wiki/Debugging#function-evaluation )


    // claim <k> runTest( #Not ( { X +Int X +Int X #Equals X *Int 3 } ) ) => . </k>
    // ^^ won't work, would be the _term_ simplifier

endmodule
