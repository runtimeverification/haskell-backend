// Copyright (c) 2016-2018 K Team. All Rights Reserved.


module VERIFICATION
  imports IMP

// verification ids
  syntax Id ::= "a"  [token]
              | "b"  [token]
              | "r"  [token]
endmodule


module UNREACHABLE-SPEC
  imports IMP
  imports VERIFICATION

  claim
    <k>
      if (a <= b) {
          if (!(a <= b)) {
              r = r + -1;
          } else {}
      } else {}
      => .K
    </k>
    <state>
      a |-> _:Int
      b |-> _:Int
      r |-> _:Int
    </state>
endmodule
