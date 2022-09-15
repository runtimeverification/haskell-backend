module LEMMAS [symbolic]
    imports BOOL
    imports INT

    syntax Int ::= bool2Word ( Bool ) [function, functional, smtlib(bool2Word)]
    // ---------------------------------------------------------------------------
    rule bool2Word( B:Bool ) => 1 requires B [simplification]

endmodule
