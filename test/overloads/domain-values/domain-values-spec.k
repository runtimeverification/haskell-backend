module VERIFICATION
  imports DOMAIN-VALUES
endmodule

module DOMAIN-VALUES-SPEC
  imports VERIFICATION
  rule <k> 1 => end </k>
  rule <k> (ctor a):Sub => end </k>
endmodule