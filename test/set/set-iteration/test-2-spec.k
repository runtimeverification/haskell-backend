requires "test.k"

module TEST-2-SPEC
  imports TEST

  claim <k> runTest( f( SetItem(X:Element) SetItem(Y:Element) ) ) </k>
    => <k> doneTest( SetItem(g(X)) SetItem(g(Y)) ) </k>
    requires
      (X =/=K Y)
      andBool (g(X) =/=K g(Y))

endmodule
