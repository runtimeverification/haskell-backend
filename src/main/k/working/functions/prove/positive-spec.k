module POSITIVE-SPEC

  imports FUNCTIONS

  // test claim
  rule
    <k> begin => end </k>
    <n> N </n>
    requires N >Int 0

  // applies only if `positive` is defined
  rule
    <k> next positive(N) => end </k>
    <n> N </n>
    [trusted]

endmodule