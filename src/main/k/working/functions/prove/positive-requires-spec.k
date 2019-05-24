module POSITIVE-REQUIRES-SPEC

  imports FUNCTIONS

  // test claim
  rule
    <k> begin => end </k>
    <n> N </n>
    requires N >Int 0

  // applies only if `positive` is defined
  rule
    <k> next _ => end </k>
    <n> N </n>
    requires positive(N)
    [trusted]

endmodule
