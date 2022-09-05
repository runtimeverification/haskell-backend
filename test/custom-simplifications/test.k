module TEST
    imports INT
    imports BOOL

    syntax Test ::= runTest( K ) | doneTest( K )

    rule <k> runTest( X ) => doneTest ( X ) ... </k>

    rule #Not ( { Y +Int Y +Int Y #Equals Y *Int 3 } ) => #Bottom [simplification]
//    rule #Not (b) => #Bottom [simplification]

endmodule
