module SETVARS
  imports K-EQUAL
  imports DOMAINS
  syntax KItem ::= Int

  syntax Int ::= f(Int) [function]
  rule f(X:Int) => X +Int 1

  syntax KItem ::= g(Int)
  rule g(@X:Int) => @X +Int 1

  syntax Int ::= h(Int) [function]
  rule h(@X:Int) => @X +Int 1

  syntax KItem ::= i(Int)
  rule i(@X:Int) => @X +Int 1 [anywhere]

endmodule