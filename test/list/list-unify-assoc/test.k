module TEST

  imports DOMAINS

  syntax Pgm ::= push( KItem )

  configuration
    <T>
      <k> $PGM:Pgm </k>
      <stack> .List </stack>
    </T>

  rule
    <k> push( X:KItem ) => . ... </k>
    <stack> .List => ListItem(X) ... </stack>

endmodule
