// Copyright (c) 2019 K Team. All Rights Reserved.

// Similar to one-spec.k, tests a basic claim, can be removed without losing
// anything.

requires "simplified.k"

module FOUR-SPEC

  imports SIMPLIFIED

  // test claim
  claim
    <k> a(g(X)) => f(g(X)) </k>

endmodule
