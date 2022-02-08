// Copyright (c) 2019 K Team. All Rights Reserved.

requires "functions.k"

module LENGTH-CONS-SPEC
  imports FUNCTIONS

  // test claim
  claim
    <k> begin => end </k>
    <n> X:KItem : XS:ConsList </n>

  // applies only if initial condition applied
  claim
    <k> next _ => end </k>
    <n> X:KItem : XS:ConsList </n>
    requires length(X : XS) >Int length(XS)
    [trusted]

endmodule
