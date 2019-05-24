module HARNESS

  imports INT-SYNTAX

  // Test harness

  syntax Cmd ::= "begin" | "next" Int | "end" Int

  configuration
    <T>
      <k> $PGM:Cmd </k>
      <n> 0 </n>
    </T>

endmodule
