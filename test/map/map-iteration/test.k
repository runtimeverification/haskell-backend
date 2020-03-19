module TEST

  imports INT
  imports MAP

  syntax Key ::= "a" | "b" | "c"

  syntax Key ::= g(Key) [function]

  rule g(a) => b
  rule g(b) => c
  rule g(c) => a
  
  syntax Int ::= h(Int) [function]

  rule h(I:Int) => I +Int 1
  
  syntax Map ::= f(Map) [function] 

  rule f(.Map) => .Map
  rule f(KEY:Key |-> VAL:Int M:Map) => g(KEY) |-> h(VAL) f(M)

endmodule
