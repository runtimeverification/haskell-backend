module TEST

  syntax State ::= "a" [token]
                 | "b" [token]
                 | "c" [token]
                 | "d" [token]
                 | "e" [token]
                 | "f" [token]

  configuration <k> $PGM:State </k>

  rule [AB]: a => b
  rule [AC]: a => c
  rule [CD]: c => d
  rule [DE]: d => e
  rule [EF]: e => f

// to produce input state:
// krun --output kore --depth 0 -cPGM=c | kore-parser definition.kore --module TEST --pattern /dev/stdin --print-pattern-json > state.json

endmodule
