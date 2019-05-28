module LENGTH-CONS-SPEC

  imports FUNCTIONS

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
