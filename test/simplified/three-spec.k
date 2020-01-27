// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIFICATION
  imports SIMPLIFIED
endmodule

module THREE-SPEC

  imports VERIFICATION

  // test claim
  rule
    <k> b(f(X)) => t(t(X)) </k>

endmodule
