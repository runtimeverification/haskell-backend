module DEMO

  imports DOMAINS

  syntax Exp ::= Exp "<=" Exp [strict]
  syntax Exp ::= Bool | Int | Id
  syntax Exp ::= "if" Exp "then" Exp "else" Exp [strict(1)]

  syntax KResult ::= Int | Bool

  configuration <k> $PGM:Exp </k> <store> .Map </store>

  rule <k> X:Id => V ...</k> <store>... X |-> V ...</store>
  rule I1:Int <= I2:Int => I1 <=Int I2

  rule if true then E1 else _ => E1
  rule if false then _ else E2 => E2

  syntax Int ::= f(Int) [function]
  rule f(X) => 1 
    requires X <=Int 0
  rule f(X) => 1 
    requires X >Int 0
endmodule
