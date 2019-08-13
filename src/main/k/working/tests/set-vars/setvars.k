module SETVARS
  imports K-EQUAL
  imports DOMAINS
  syntax KItem ::= Int
  syntax KResult ::= Int

  syntax Int ::= f(Int) [function]
  rule f(X:Int) => X +Int 1

  syntax KItem ::= g(Int)
  rule g(@X:Int) => @X +Int 1 // This is not yet supported

  syntax Int ::= h(Int) [function]
  rule h(@X:Int) => @X +Int 1

  syntax KItem ::= i(Int)
  rule i(@X:Int) => @X +Int 1 [anywhere]

  syntax Int ::= j(Int, Int) [function, functional]

  rule j(X:Int,Y:Int) => X /Int Y requires Y =/=Int 0
  rule j(X:Int,0) => 1
//  rule j(X:Int,error(_)) => X
/*
  rule
    #Ceil(@I1:Int /Int @I2:Int)
  =>
    {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)
  [anywhere]
*/
endmodule