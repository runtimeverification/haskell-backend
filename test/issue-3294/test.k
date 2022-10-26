module TEST
  imports SET
  imports BOOL

  syntax Thing ::= "a" | "b"

  syntax Test ::= intersect ( Set ) | result ( Set )

  rule intersectSet ( S SetItem(X), S) => S
                    ensures notBool (X in S) [simplification]

  configuration <k> $PGM:Test </k>

  rule <k> intersect(E) => result(E) </k>

endmodule
