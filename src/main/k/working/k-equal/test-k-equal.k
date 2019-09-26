require "domains.k"

module TEST-K-EQUAL
    imports BOOL
    imports INT
    imports K-EQUAL

    configuration <T> <k> $PGM:Pgm </k> </T>

    syntax Pgm ::= #done( Int )

    syntax Pgm ::= #iszero( Int )
    rule <k> #iszero( I:Int ) => #done( bool2Int( I ==Int 0 ) ) </k>

    syntax Int ::= bool2Int( Bool ) [function, functional]
    rule bool2Int( B:Bool ) => 1 requires B
    rule bool2Int( B:Bool ) => 0 requires notBool B
endmodule
