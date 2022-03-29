// Copyright (c) 2019 K Team. All Rights Reserved.

// Similar to two-spec.k, but with simplification axioms instead of function
// definition ones.
//
// Tests that we can evaluate simplification axiom branches when the actual
// branching is done through rewrite rules.
//
// Expected execution:
// bb(x) => (cc(x) and x>0) or (dd(x) and x<=0)
// cc(x) and x>0 => aa(x) and x>0 => g(x) and x>0 ~= s(x) and x>0
// dd(x) and x<=0 => aa(x) and x>0 => g(x) and x<=0 ~= s(x) and x<=0

requires "simplified.k"

module SIX-SPEC

  imports SIMPLIFIED

  // test claim
  claim
    <k> bb(X) => s(X) </k>

endmodule
