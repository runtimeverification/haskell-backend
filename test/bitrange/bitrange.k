module BITRANGE
  imports DOMAINS
  syntax Exp ::= Int
  syntax Exp ::= bRI           ( Int, indexInt: Int, lengthInt: Int ) [function]
               | "[" Exp "]" [function]

  rule bRI(I, IDX, LEN) => (I >>Int IDX) modInt (1 <<Int LEN)
  rule [ I:Int ] => I
endmodule
