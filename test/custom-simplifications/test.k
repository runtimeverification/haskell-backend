module TEST
    imports INT
    imports BOOL

    syntax Test ::= runTest( K ) | doneTest( K )

    rule <k> runTest( X ) => doneTest ( X ) ... </k>

    rule [IntegerArithmeticErrorIsBottom]:
      #Not ( { Y +Int Y +Int Y #Equals Y *Int 3 } ) => #Bottom [simplification]

endmodule
