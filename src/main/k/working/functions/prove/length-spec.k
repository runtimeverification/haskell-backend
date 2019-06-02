// Copyright (c) 2019 K Team. All Rights Reserved.


module VERIFICATION
  imports FUNCTIONS
endmodule

module LENGTH-SPEC

  imports VERIFICATION

  // test claim
  rule
    <k> begin => end </k>
    <n> LIST:ConsList </n>
    requires length(LIST) >Int 1

  // applies only if initial condition applied
  rule
    <k> next _ => end </k>
    <n> LIST:ConsList </n>
    requires length(LIST) >Int 1
    [trusted]

endmodule
