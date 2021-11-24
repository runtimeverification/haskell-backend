module VERIFICATION
  imports TEST

endmodule

module TEST-SPEC
  imports VERIFICATION

  claim a(X, Y) => .K requires f(X, Y) <Int 0

endmodule
