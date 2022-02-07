// Testing that the smt-lemma works by proving that
// the final configuration is equivalent to 5<Int X

requires "smt-lemma.k"

module ONE-SPEC
  imports SMT-LEMMA

  claim
    <k> delayed(X:Int)
    => 5 <Int X
    </k>

endmodule
