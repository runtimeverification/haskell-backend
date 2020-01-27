// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIFICATION
  imports SIMPLIFIED
endmodule

module FOUR-SPEC

  imports VERIFICATION

  // test claim
  rule
    <k> a(g(X)) => f(g(X)) </k>

endmodule
