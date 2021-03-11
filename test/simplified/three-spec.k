// Copyright (c) 2019 K Team. All Rights Reserved.

// Also read the explanation for two-spec.k.
//
// This tests that we reevaluate functions when the top-level condition changes
//
// Expected execution:
// 1. b(f(x)) is simplified to itself, with both b(f(x)) and its subterm, f(x),
//    being marked as simplified while the top condition is 'top'
// 2. b(f(x)) => (c(f(x)) and x>0) or (d(f(x)) and x<=0)
// 3. c(f(x)) and x>0 is simplified to c(t(x))
// 4. d(f(x)) and x<=0 is simplified to d(t(x))
// 5. c(t(x)) and x>0
//    => a(t(x)) and x>0
//    => f(t(x)) and x>0
//    == t(t(x)) and x>0
// 6. d(t(x)) and x<=0
//    => a(t(x)) and x>0
//    => f(t(x)) and x<=0
//    == t(t(x)) and x<=0

module VERIFICATION
  imports SIMPLIFIED
endmodule

module THREE-SPEC

  imports VERIFICATION

  // test claim
  claim
    <k> b(f(X)) => t(t(X)) </k>

endmodule
