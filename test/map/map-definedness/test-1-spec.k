module VERIFICATION
  imports TEST
endmodule

module TEST-1-SPEC
  imports VERIFICATION

  rule
    <k> add(X, 3) => end </k>
    <a> Y:Int |-> 2 M:Map => ?_ </a>

endmodule
