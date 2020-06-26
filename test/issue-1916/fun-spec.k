module VERIFICATION
  import TEST
endmodule

module FUN-SPEC
  import VERIFICATION

  rule <k> begin => end </k> requires isFun(X) ensures true #And #Ceil(fun(X))
endmodule