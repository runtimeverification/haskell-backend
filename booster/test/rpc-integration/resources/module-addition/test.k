module TEST

  syntax State ::= "a" [token]
                 | "b" [token]
                 | "c" [token]
                 | "d" [token]

  // we need a k cell with a kseq in it to have proper indexing
  configuration <k> $PGM:State ~> .K </k>

  rule [AB]: <k> a => b ... </k>
  rule [AC]: <k> a => c ... </k>
  rule [CD]: <k> c => d ... </k>

// to produce input state:
// krun --output kore --depth 1 -cPGM=c | kore-parser definition.kore --module TEST --pattern /dev/stdin --print-pattern-json > state.json

endmodule
