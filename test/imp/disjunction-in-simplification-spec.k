/*
*/

module VERIFICATION
  imports IMP

  syntax Id ::= "a" [token]
  syntax Id ::= "b" [token]
  syntax Id ::= "x" [token]
  syntax AExp ::= choice (AExp, AExp) [strict]
  rule choice(A:Int, B:Int) => A #Or B [simplification, anywhere]
endmodule


module DISJUNCTION-IN-SIMPLIFICATION-SPEC
  imports VERIFICATION
  imports IMP

  rule
    <k>
      x = choice(a, b) ;
      => .K
    </k>
    <state>
      a   |-> A:Int
      b   |-> B:Int
      x |-> (_ => ?X:Int)
    </state>
  ensures
    ?X ==Int A orBool ?X ==Int B

endmodule
