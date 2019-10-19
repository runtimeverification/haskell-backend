module VERIFICATION
  imports DEMO

  syntax Id ::= "x" [token]
  syntax Id ::= "s" [token]
endmodule

module DEMO-SPEC
  imports VERIFICATION

  rule <k> if x <= 0 then 2 else 2 => 2 </k>
    <store> x |-> X:Int s |-> (X:Int modInt 7 => 0) </store>
    requires f(X) <=Int 0
endmodule
