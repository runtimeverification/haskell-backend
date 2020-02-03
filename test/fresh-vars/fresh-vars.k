module FRESH-VARS
  imports INT
  imports BOOL
  syntax KResult ::= Int

  syntax Exp ::= Int
	       | Exp "+" Exp [strict]
  
  syntax Exp ::= "foo" "(" Int ")"
  rule foo(N) => ?_:Int + foo(N -Int 1)
    requires N >Int 0
  rule foo(0) => 0
  rule I1:Int + I2:Int => I1 +Int I2

  syntax X ::= "foo"
  rule <k> foo => foo(3) </k>
endmodule
