module VERIFICATION
  imports PATH

endmodule

module IDENTITY-SPEC
  imports VERIFICATION
  imports PATH

  rule <k> a => a </k> [all-path]

endmodule
