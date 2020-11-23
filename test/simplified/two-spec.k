// Copyright (c) 2019 K Team. All Rights Reserved.

// Tests that we can evaluate function branches when the actual branching
// is done through rewrite rules.
//
// Note that this test is interesting only because the Haskell backend
// does not branch when evaluating functions, so a(x) would always rewrite
// to f(x), which, without any side condition, would branch, so it would remain
// unevaluated
//
// Expected execution:
// b(x) => (c(x) and x>0) or (d(x) and x<=0)
// c(x) and x>0 => a(x) and x>0 => f(x) and x>0 == t(x) and x>0
// d(x) and x<=0 => a(x) and x>0 => f(x) and x<=0 == t(x) and x<=0

module VERIFICATION
  imports SIMPLIFIED
endmodule

module TWO-SPEC

  imports VERIFICATION

  // test claim
  claim
    <k> b(X) => t(X) </k>

endmodule
