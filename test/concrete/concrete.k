module CONCRETE
  imports BOOL

  syntax Val ::= "a"

  syntax Val ::= f(Val) [function, total]
  rule f(X) => a [concrete]

  syntax Val ::= g() [function, total]
endmodule
