requires "infinite-gas.k"

module INFINITE-GAS-SPEC
    imports INFINITE-GAS

    claim <k> runLemma(#gas(GAVAIL) <Int log2Int(G0) +Int 1)  => doneLemma(false) ... </k> requires 0 <Int G0 andBool G0 <=Int 1

endmodule
