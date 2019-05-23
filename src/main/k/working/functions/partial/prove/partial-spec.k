module PARTIAL-SPEC

imports PARTIAL

rule
  <k> begin => end partially(N, 1) </k>
  <n> N </n>
  requires N >=Int 0

endmodule
