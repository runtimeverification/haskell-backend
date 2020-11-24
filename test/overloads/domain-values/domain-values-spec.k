module VERIFICATION
  imports DOMAIN-VALUES
endmodule

module DOMAIN-VALUES-SPEC
  imports VERIFICATION
  claim <k> 1 => end </k>
  claim <k> (ctor a):Sub => end </k>
endmodule