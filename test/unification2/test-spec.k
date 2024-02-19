module TEST-SPEC
  imports TEST

  claim <k>(mapLookup(address(X), address(X) |-> u(_) M:Map) => ?_:Maybe) ~> M:Map ~> _:K </k>
endmodule
