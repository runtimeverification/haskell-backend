module VERIFICATION
  imports TEST

endmodule

module TEST-SPEC
  imports VERIFICATION

  claim b(keys(_M:Map)) => c

endmodule
