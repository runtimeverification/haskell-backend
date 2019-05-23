module PARTIAL

imports INT

// functions
syntax Cmd ::= "begin" | "next" Int | "end" Int

configuration
  <T>
    <k> $PGM:Cmd </k>
    <n> 0 </n>
  </T>

rule <k> begin => next 0 </k>

syntax Int ::= partially(Int, Int) [function]

rule partially(M, I) => 0  requires I >Int M

rule
  <k> next partially(N, N +Int 1) => end partially(N, 1) </k>
  <n> N </n>
  requires N >=Int 0

endmodule
