module TEST
  imports INT
  imports K-EQUAL

  syntax KItem ::= a(Int, Int) | "stuck"
  syntax Int ::= f(Int, Int)  [function, functional]

  rule [f-main]: f(X, X) => -1
  rule [f-owise]: f(X, Y) => 1  [owise]

  rule a(X, X) => .K
  rule a(X, Y) => stuck requires X =/=K Y

endmodule
