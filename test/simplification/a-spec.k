module VERIFICATION

    imports SIMPLIFICATION

    rule [f.positive]: f(X:Int) => a requires X >Int 0 [simplification]
    rule [f.negative]: f(X:Int) => b requires X <Int 0 [simplification]

endmodule

module A-SPEC

    imports VERIFICATION

    claim <k> f(X:Int) => a </k>

endmodule