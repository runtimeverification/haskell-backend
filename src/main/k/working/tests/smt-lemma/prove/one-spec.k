// Testing that the smt-lemma works by proving that
// the final configuration is equivalent to 5<Int X
module VERIFICATION
  imports SMT-LEMMA
endmodule

module ONE-SPEC
  imports VERIFICATION

  rule
    <k> delayed(X:Int)
    => 5 <Int X
    </k>

endmodule
