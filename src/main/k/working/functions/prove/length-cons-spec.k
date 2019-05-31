// Copyright (c) 2019 K Team. All Rights Reserved.


module VERIFICATION
  imports FUNCTIONS
endmodule

module LENGTH-CONS-SPEC

  imports VERIFICATION

  // test claim
  rule
    <k> begin => end </k>
    <n> X:KItem : XS:ConsList </n>

  // applies only if initial condition applied
  rule
    <k> next _ => end </k>
    <n> X:KItem : XS:ConsList </n>
    requires length(X : XS) >Int length(XS)
    [trusted]

endmodule
