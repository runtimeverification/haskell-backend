module LENGTH-SPEC

  imports FUNCTIONS

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
