// Testing that the smt-lemma works by proving that
// the final configuration is equivalent to 5<Int X

requires "smt-lemma.k"

module VERIFICATION
  imports SMT-LEMMA
endmodule

module ONE-SPEC
  imports VERIFICATION

  claim
    <k> delayed(X:Int)
    => 5 <Int X
    </k>

endmodule
