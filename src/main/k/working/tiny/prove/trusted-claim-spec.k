module VERIFICATION
  imports TINY

endmodule

module TRUSTED-CLAIM-SPEC
  imports VERIFICATION
  imports TINY

  rule a => c

  rule b => c [trusted]

endmodule
