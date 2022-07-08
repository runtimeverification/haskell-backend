module TEST
  imports BOOL
  imports INT
  imports MAP

  syntax Address ::= address(Int)
  syntax U ::= u(Int)
  syntax Maybe ::= just(KItem) | "nothing"

  syntax KItem ::= mapLookup(KItem, Map)

  rule [r]: mapLookup(K:KItem, ((K |-> V:KItem) _:Map) #as M:Map) => just(V)
    ensures K in_keys(M)
endmodule
