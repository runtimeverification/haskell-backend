requires "locals.k"

module VERIFICATION
  imports LOCALS
endmodule

module LOCALS-SPEC
  imports VERIFICATION

  claim
    <k> begin X:Int => end V:Value </k>
    <locals> X:Int |-> V:Value </locals>
endmodule
