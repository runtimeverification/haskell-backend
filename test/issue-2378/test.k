// Copyright (c) 2020 K Team. All Rights Reserved.

module TEST
  imports SET
  imports MAP

  syntax B  ::= b(Set)
            | "c"
  syntax KItem ::= B

  rule b(.Set) => c
  rule b(SetItem(_:KItem) S:Set) => b(S)

endmodule
