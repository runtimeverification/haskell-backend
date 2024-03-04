module SIMPLE-EXPS
  imports INT
  syntax Exp ::= Val
  syntax Exp ::= Exp "+" Exp             [strict]
  syntax Exp ::= "[" Exps "]"            [strict]
  syntax Exps ::= List{Exp,","}          [overload(_,_), strict]
  syntax Exp ::= length(Exp)             [strict]

  syntax KResult ::= Val | Vals

  syntax Val ::= Int
  syntax Val ::= vals(Vals)
  syntax Vals ::= List{Val,","}          [overload(_,_), strict]
  syntax Exps ::= Vals

  configuration <k> $PGM:Exp </k>

  rule I1:Int + I2:Int => I1 +Int I2

  rule [Vs:Vals] => vals(Vs)

  rule length(vals(.Vals)) => 0
  rule length(vals(V:Val,L:Vals)) => 1 + length(vals(L))
endmodule
