// Copyright (c) 2019 K Team. All Rights Reserved.

// Base test that a rewrite we use in all the other tests works as expected.
// Can be removed from the current test suite without losing anything.

requires "simplified.k"

module ONE-SPEC

  imports SIMPLIFIED

  // test claim
  claim
    <k> a(X) => f(X) </k>

endmodule
