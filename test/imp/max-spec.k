/*
*/

requires "imp.k"

module MAX-SPEC
  imports IMP

  claim
    <k>
      if (a <= b) {
          max = b;
      } else {
          max = a;
      }
      => .K
    </k>
    <state>
      a   |-> A:Int
      b   |-> B:Int
      max |-> (_ => ?M:Int)
    </state>
  ensures
    (A >=Int B andBool ?M ==Int A) orBool (B >=Int A andBool ?M ==Int B)

endmodule
