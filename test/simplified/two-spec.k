// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIFICATION
  imports SIMPLIFIED
endmodule

module TWO-SPEC

  imports VERIFICATION

  // test claim
  rule
    <k> b(X) => t(X) </k>

endmodule
