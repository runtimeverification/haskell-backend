module FRESH-VARS
  imports INT
  imports BOOL
  
  syntax Seq ::= List{Int, ":"}
  syntax Seq ::= "foo" "(" Int ")" [function]
  rule foo(N) => ?_:Int : foo(N -Int 1)
    requires N >Int 0
  rule foo(0) => .Seq

  syntax X ::= "foo"
  rule <k> foo => foo(3) </k>
endmodule
