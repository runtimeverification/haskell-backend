module VERIFICATION
  imports SIMPLE-LISTS
endmodule

module BROKEN-SPEC
  imports VERIFICATION

  rule i1 i2 => d1 d2
endmodule