module HARNESS

  imports BOOL-SYNTAX
  imports INT-SYNTAX

  // Test harness

  syntax Cmd ::= "begin" | "next" Bool | "end"

  configuration
    <T>
      <k> $PGM:Cmd </k>
      <n> 0:Int </n>
    </T>

endmodule
