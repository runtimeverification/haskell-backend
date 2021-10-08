module STRICT
  imports INT
  imports BOOL

  syntax Exp ::= Int
               | checkInterval(Int, Int, Exp) [strict(3)]
               | interval(Int, Int)
  syntax KResult ::= Int

  rule interval(I:Int, J:Int) => ?X:Int
      ensures ?X >=Int I
      andBool ?X <=Int J

  rule checkInterval(I:Int, J:Int, X:Int) => 1
      requires X >=Int I
      andBool  X <=Int J
endmodule
