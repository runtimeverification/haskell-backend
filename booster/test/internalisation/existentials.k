module EXISTENTIALS

  syntax Foo ::= Foo() | Bar()

  syntax Baz ::= Baz(Foo) | Beep(Foo, Baz)

  rule Baz(Foo()) => Baz(Bar())
  rule Baz(Bar()) => Beep(?Any, ?Other)

endmodule
