// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIFICATION
  imports SIMPLIFIED
endmodule

module SIX-SPEC

  imports VERIFICATION

  // test claim
  rule
    <k> bb(X) => s(X) </k>

endmodule
