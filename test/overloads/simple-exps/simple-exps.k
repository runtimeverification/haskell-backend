module SIMPLE-EXPS
  imports INT
  syntax Val ::= Int
  syntax Exp ::= Val
  syntax Exp ::= Exp "+" Exp             [strict]
  syntax Exp ::= "[" Exps "]"
  syntax Exp ::= length(Exps)
  syntax Exps ::= List{Exp,","}          [overload(_,_)]
  syntax Vals ::= List{Val,","}          [overload(_,_)]
  syntax Exps ::= Vals

  rule [Vs:Vals] => length(Vs)

  rule length((_:Exp, Es:Exps)) => 1 + length(Es)
  rule length(.Exps) => 0

  syntax KResult ::= Val

  rule I1:Int + I2:Int => I1 +Int I2

  configuration <k> $PGM:Exp </k>
endmodule
