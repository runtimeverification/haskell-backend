module SIMPLE-EXPS
  imports INT
  syntax Val ::= Int
  syntax Exp ::= Val
  syntax Exp ::= Exp "+" Exp             [strict]
  syntax Exp ::= "[" Exps "]"            [strict]
  syntax Exps ::= List{Exp,","}          [klabel(_,_)]  // automatically hybrid now
  syntax Vals ::= List{Val,","}          [klabel(_,_)]
  syntax Exps ::= Vals

  syntax Val ::= vals(Vals)

  rule [Vs:Vals] => vals(Vs)

  syntax KResult ::= Val | Vals

  rule I1:Int + I2:Int => I1 +Int I2

  configuration <k> $PGM:Exp </k>
endmodule
