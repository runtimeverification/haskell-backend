// Copyright (c) 2019 K Team. All Rights Reserved.


module VERIFICATION
  imports FUNCTIONS
endmodule

module POSITIVE-REQUIRES-SPEC

  imports VERIFICATION

  // test claim
  claim
    <k> begin => end </k>
    <n> N </n>
    requires N >Int 0

  // applies only if `positive` is defined
  claim
    <k> next _ => end </k>
    <n> N </n>
    requires positive(N)
    [trusted]

endmodule
