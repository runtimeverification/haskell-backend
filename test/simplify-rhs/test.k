module TEST
    
    syntax S ::= "a" | "b" | "c" | "evaluated"
               | f(S) [function]

    rule f(_:S) => evaluated

    rule a => f(b)

endmodule
