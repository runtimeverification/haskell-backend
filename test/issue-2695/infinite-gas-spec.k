module VERIFICATION
    imports INFINITE-GAS

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Bool
 // --------------------

endmodule

module INFINITE-GAS-SPEC
    imports VERIFICATION

    claim <k> runLemma(#gas(GAVAIL) <Int log2Int(G0) +Int 1)  => doneLemma(false) ... </k> requires 0 <Int G0 andBool G0 <=Int 1

endmodule