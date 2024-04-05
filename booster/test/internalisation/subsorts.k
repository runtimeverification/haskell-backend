module SUBSORTS-A

  syntax A1 ::= A1()

  syntax A2 ::= A1 | A2()

  syntax A3 ::= A3()

endmodule

// A1 < A2; A3

module SUBSORTS-B
  imports SUBSORTS-A
  imports BOOL

  // new supersort of SubA1 and SubA2
  syntax B1 ::= A1 | A2 // will A1 be eliminated?

  // existing sort A3 made a supersort of Bool
  syntax A3 ::= Bool
endmodule

// A1 < A2 < B1; Bool < A3

module SUBSORTS-C
  imports SUBSORTS-A

  // new subsort of A1
  syntax C1 ::= C1()
  syntax A1 ::= C1

  // existing sort A2 made a subsort of a new sort
  syntax C2 ::= A2 | C2()

endmodule

// C1 < A1 < A2 < C2; A3


module SUBSORTS
  imports SUBSORTS-B
  imports SUBSORTS-C

// C1 < A1 < A2 < [B1, C2] ; Bool < A3

endmodule
