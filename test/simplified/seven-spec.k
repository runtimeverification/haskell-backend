// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIFICATION
  imports SIMPLIFIED
endmodule

module SEVEN-SPEC

  imports VERIFICATION

  // test claim
  rule
    <k> bb(g(X)) => s(s(X)) </k>

endmodule
