module VERIFICATION
  imports TINY

endmodule

module MIXED-CLAIMS-SPEC
  imports VERIFICATION
  imports TINY

  claim b => d [one-path]
  
  claim a => d [all-path]

endmodule
