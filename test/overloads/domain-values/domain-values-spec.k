requires "domain-values.k"

module DOMAIN-VALUES-SPEC
  imports DOMAIN-VALUES
  claim <k> 1 => end </k>
  claim <k> (ctor a):Sub => end </k>
endmodule