module PRESERVES-DEFINEDNESS-TOTAL-FUNCTION
  syntax Foo ::= Foo() | Baz() | Bar() | frob(Foo) [function, total, symbol]

  rule <k> Foo() ~> K:K </k> => <k> frob(Bar()) ~> K </k>

endmodule
