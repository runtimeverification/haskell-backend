module TEST
    imports MAP
    imports BOOL

    syntax Foo ::= "a" | "b" | "c"
 // ------------------------------
    rule <k> a => b ... </k>

endmodule
