module TEST
    imports INT
    imports BOOL

    rule {I +Int J #Equals I +Int K} => #Bottom
        requires notBool J ==Int K [simplification]

    syntax Test ::= runTest( K ) | doneTest( K )

    rule <k> runTest( X ) => doneTest ( X ) ... </k>

endmodule
