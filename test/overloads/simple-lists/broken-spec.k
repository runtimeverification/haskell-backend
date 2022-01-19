requires "simple-lists.k"

module VERIFICATION
  imports SIMPLE-LISTS
endmodule

module BROKEN-SPEC
  imports VERIFICATION

  claim i1 i2 => d1 d2
endmodule