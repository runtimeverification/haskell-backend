module CEIL-SET-SYNTAX
    imports SET
    imports K-EQUAL
    imports BOOL

    syntax Test ::= eval ( Set ) | evalResult ( Set )
endmodule

module CEIL-SET
    imports CEIL-SET-SYNTAX

    configuration <k> $PGM:Test </k>

    rule <k> eval ( S ) => evalResult ( S ) </k>

    rule [setCeil]: #Ceil(@S1:Set @S2:Set) => {intersectSet(@S1, @S2) #Equals .Set} #And #Ceil(@S1) #And #Ceil(@S2)
      [simplification]

endmodule
