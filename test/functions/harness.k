module HARNESS

  imports BASIC-K
  imports LIST
  imports INT

  // Test harness

  syntax Cmd ::= "begin" | "next" KItem | "end"

  configuration
    <T>
      <k> $PGM:Cmd </k>
      <n> 0:KItem </n>
    </T>

endmodule
