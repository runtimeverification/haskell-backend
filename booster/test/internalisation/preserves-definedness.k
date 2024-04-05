module PRESERVES-DEFINEDNESS
  syntax Foo ::= Foo() | Baz() | Bar() | frob(Foo) [function, symbol]

  rule <k> Foo() ~> K:K </k> => <k> Bar() ~> K </k>

endmodule
