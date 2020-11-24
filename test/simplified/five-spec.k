// Copyright (c) 2019 K Team. All Rights Reserved.

// Similar to one-spec.k, tests a basic claim, can be removed without losing
// anything.

module VERIFICATION
  imports SIMPLIFIED
endmodule

module FIVE-SPEC

  imports VERIFICATION

  // test claim
  claim
    <k> aa(X) => g(X) </k>

endmodule
