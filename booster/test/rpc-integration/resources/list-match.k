module TEST
  imports INT
  imports BOOL
  imports LIST

  configuration <k> $PGM:Pgm </k>

  syntax Pgm ::= foo() | bar()

  rule foo() => bar() ensures size(ListItem(?A:Int) ListItem(?B:Int) ?L:List) >Int 0
  rule [simplify-size]: size(ListItem(_) WS) => size(WS) +Int 1 [simplification]

  rule [helper]: size(_:List) +Int A >Int 0 => true requires A >Int 0 [simplification]

endmodule
