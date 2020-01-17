module CONCRETE
  imports BOOL

  syntax Val ::= "a"

  syntax Val ::= f(Val) [function, functional]
  rule f(X) => a [concrete]

  syntax Val ::= g() [function, functional]
endmodule
