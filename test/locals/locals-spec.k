requires "locals.k"

module LOCALS-SPEC
  imports LOCALS

  claim
    <k> begin X:Int => end V:Value </k>
    <locals> X:Int |-> V:Value </locals>
endmodule
