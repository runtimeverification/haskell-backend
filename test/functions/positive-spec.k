// Copyright (c) 2019 K Team. All Rights Reserved.

requires "functions.k"

module POSITIVE-SPEC

  imports FUNCTIONS

  // test claim
  claim
    <k> begin => end </k>
    <n> N </n>
    requires N >Int 0

  // applies only if `positive` is defined
  claim
    <k> next positive(N) => end </k>
    <n> N </n>
    [trusted]

endmodule
