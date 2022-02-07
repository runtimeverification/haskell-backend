// Copyright (c) 2016-2018 K Team. All Rights Reserved.

requires "imp.k"

module UNREACHABLE-SPEC
  imports IMP

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
