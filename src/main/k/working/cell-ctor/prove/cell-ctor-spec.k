// Copyright (c) 2019 K Team. All Rights Reserved.


module VERIFICATION
  imports CELL-CTOR
endmodule

module CELL-CTOR-SPEC

  imports VERIFICATION

  // The backend will have to prove that <n> _ </n> has only one constructor
  // because that cell is omitted here, but the corresponding rule in the
  // definition mentions it.
  rule <k> begin => end </k>

endmodule
