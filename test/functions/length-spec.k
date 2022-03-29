// Copyright (c) 2019 K Team. All Rights Reserved.

requires "functions.k"

module LENGTH-SPEC

  imports FUNCTIONS

  // test claim
  claim
    <k> begin => end </k>
    <n> LIST:ConsList </n>
    requires length(LIST) >Int 1

  // applies only if initial condition applied
  claim
    <k> next _ => end </k>
    <n> LIST:ConsList </n>
    requires length(LIST) >Int 1
    [trusted]

endmodule
