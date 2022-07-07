module TEST-SPEC
  imports TEST

  claim (mapLookup(address(X), address(X) |-> u(_) M:Map) => ?_:Maybe) ~> M:Map ~> _:K
endmodule
