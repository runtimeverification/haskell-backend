module TEST

  imports BOOL
  imports LIST

  syntax Val ::= "a" | "b" | "c"

  configuration
    <T>
      <k> $PGM:Val </k>
      <l> ListItem(a) ListItem(b) ListItem(c) </l>
      <v> .K </v>
    </T>

  rule
    <k> V:Val </k>
    <l> ListItem(V) ... </l>
    <v> .K => V </v>

endmodule
