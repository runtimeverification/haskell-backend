module TEST
    imports BOOL
    imports INT

    configuration <k> $PGM:Int </k>

    rule <k> X => X +Int 1 ... </k> requires X <=Int 10

endmodule
