// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIFICATION
  imports SIMPLIFIED
endmodule

module FIVE-SPEC

  imports VERIFICATION

  // test claim
  rule
    <k> aa(X) => g(X) </k>

endmodule
