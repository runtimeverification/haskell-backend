module TEST

  imports INT
  imports MAP

  syntax Val ::= "added" | add(Int, Int) | "end"

  syntax Int ::= f(Int) [function]

  rule f(6) => 7

  configuration
    <T>
      <k> $PGM:Val </k>
      <a> .Map </a>
    </T>

  rule
    <k> add(KEY:Int, VAL:Int) => added ... </k>
    <a> M:Map => (KEY |-> VAL) M </a>

  rule
    <k> added => end </k>

endmodule
