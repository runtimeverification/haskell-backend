module VERIFICATION
  imports TINY

endmodule

module MIXED-CLAIMS-SPEC
  imports VERIFICATION
  imports TINY

  rule b => d [one-path]
  
  rule a => d [all-path]

endmodule
