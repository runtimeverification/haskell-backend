// Copyright (c) 2019 K Team. All Rights Reserved.


module VERIFICATION
  imports SIMPLIFIED
endmodule

module ONE-SPEC

  imports VERIFICATION

  // test claim
  rule
    <k> a(X) => f(X) </k>

endmodule
