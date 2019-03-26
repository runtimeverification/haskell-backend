// Testing that the smt-lemma works by proving that
// the final configuration is equivalent to 5<Int X
module ONE-SPEC
  imports TEST

  rule
    <k> delayed(X:Int)
    => 5 <Int X
    </k>

endmodule
