// Copyright (c) 2019 K Team. All Rights Reserved.

module MAP-TESTS-SYNTAX
    imports MAP
    imports INT

    syntax MyId ::= "x" | "y" | "z" | foo ( MyId )

    syntax Test ::= Int | Map
                  | remove ( K ) | removeResult ( K )

endmodule

module MAP-TESTS
    imports MAP-TESTS-SYNTAX
    imports MAP-SYMBOLIC

    configuration <k> $PGM:Test </k>

    rule <k> remove ( K ) => removeResult ( K ) </k>

endmodule
