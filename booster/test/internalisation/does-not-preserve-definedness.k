module DOES-NOT-PRESERVE-DEFINEDNESS
  syntax Foo ::= Foo() | Baz() | Bar() | frob(Foo) [function, symbol]

  rule <k> Foo() ~> K:K </k> => <k> frob(Bar()) ~> K </k>

endmodule
