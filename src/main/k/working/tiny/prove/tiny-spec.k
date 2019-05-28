module VERIFICATION
  imports TINY

endmodule

module TINY-SPEC
  imports VERIFICATION
  imports TINY

  rule a => c

  rule b => c [trusted]

endmodule
