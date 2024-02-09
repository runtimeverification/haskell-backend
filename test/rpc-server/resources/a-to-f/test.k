module TEST
  imports INT
  imports BOOL

  syntax State ::= "a" [token]
                 | "b" [token]
                 | "c" [token]
                 | "d" [token]
                 | "e" [token]
                 | "f" [token]

  configuration <T>
                  <k> $PGM:State </k>
                  <val> 0 </val>
                </T>

  rule [AB]: <k> a => b ... </k> <val> V </val> requires V ==Int 0
  rule [AC]: <k> a => c ... </k> <val> V </val> requires notBool (V ==Int 0)
  rule [CD]: c => d
  rule [DE]: d => e
  rule [EF]: e => f

// to produce input state:
// krun --output kore --depth 0 -cPGM=c | kore-parser definition.kore --module TEST --pattern /dev/stdin --print-pattern-json > state.json

endmodule
