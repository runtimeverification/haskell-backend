module TEST

  imports BOOL
  imports LIST

  syntax Pgm ::= push( KItem )

  configuration
    <T>
      <k> $PGM:Pgm </k>
      <stack> .List </stack>
    </T>

  rule
    <k> push( X:KItem ) => .K ... </k>
    <stack> .List => ListItem(X) ... </stack>

endmodule
