requires "domains.md"

module EVM
    imports INT
    imports BOOL

    configuration
        <k> $PGM:EthereumSimulation </k>
    syntax EthereumSimulation

endmodule

module INFINITE-GAS
    imports EVM

    syntax Int ::= #gas ( Int ) [function, functional, no-evaluators, klabel(infGas), symbol, smtlib(infGas)]
 // ---------------------------------------------------------------------------------------------------------
    rule #gas(_) <Int I          => false requires I <=Int 1                                       [simplification]
    rule #gas(G) <Int I +Int I'  => false requires notBool (#gas(G) <Int I orBool #gas(G) <Int I') [simplification]

 // for infinite-gas-spec:

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Bool
 // --------------------

endmodule
