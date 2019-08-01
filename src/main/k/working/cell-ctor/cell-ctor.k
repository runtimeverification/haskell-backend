module CELL-CTOR

  imports DOMAINS

  // Test harness

  syntax Cmd ::= "begin" | "end"

  configuration
    <T>
      <k> $PGM:Cmd </k>
      <n> 0:Int </n>
    </T>

  rule
    <k> begin => end </k>
    <n> N </n>

endmodule
