module TEST
    imports INT

    syntax Pgm ::= foo(Int)
    rule <k> foo(I) => foo(I -Int 1) ... </k>
endmodule