// Copyright (c) 2019 K Team. All Rights Reserved.

// Similar to three-spec.k, but with simplification axioms instead of function
// definition ones.
//
// This tests that we retry simplification axioms when the top-level condition
// changes.
//
// Expected execution:
// 1. bb(g(x)) is simplified to itself, with both bb(g(x)) and its subterm,
//    g(x), being marked as simplified while the top condition is 'top'
// 2. b(g(x)) => (cc(g(x)) and x>0) or (dd(g(x)) and x<=0)
// 3. cc(g(x)) and x>0 is simplified to cc(s(x))
// 4. dd(g(x)) and x<=0 is simplified to dd(s(x))
// 5. cc(s(x)) and x>0
//    => aa(s(x)) and x>0
//    => g(s(x)) and x>0
//    ~= s(s(x)) and x>0
// 6. dd(s(x)) and x<=0
//    => aa(s(x)) and x>0
//    => g(s(x)) and x<=0
//    ~= s(s(x)) and x<=0

requires "simplified.k"

module VERIFICATION
  imports SIMPLIFIED
endmodule

module SEVEN-SPEC

  imports VERIFICATION

  // test claim
  claim
    <k> bb(g(X)) => s(s(X)) </k>

endmodule
