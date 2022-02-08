module SIMPLIFICATION

    imports INT
    syntax S ::= f(Int) [function]
                | "a"
                | "b"

    // for a-spec
    rule [f.positive]: f(X:Int) => a requires X >Int 0 [simplification]
    rule [f.negative]: f(X:Int) => b requires X <Int 0 [simplification]

endmodule