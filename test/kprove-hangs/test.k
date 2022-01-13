module TEST
    imports DEFAULT-CONFIGURATION

    syntax Foo ::= "a" | "b" | "c"
 // ------------------------------
    rule <k> a => b ... </k>

endmodule
