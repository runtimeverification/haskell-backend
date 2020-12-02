module VERIFICATION
  imports TEST
endmodule

module TEST-2-SPEC
  imports VERIFICATION

  claim
    <k> add(X, 3) => end </k>
    <a> 2 |-> 3 M N => ?_ </a>

endmodule
