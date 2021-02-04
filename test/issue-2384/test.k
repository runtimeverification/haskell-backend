module TEST
  imports BOOL
  imports INT
  imports MAP

  syntax KResult ::= Int

  syntax A ::= a(Map) | "b"

  rule [xyzzy]: X:KItem in_keys((Y:KItem |-> _:KItem M:Map))
        => X ==K Y orBool X in_keys(M)
    [simplification]

  rule a(M:Map) => b
    requires 3 in_keys(M)

endmodule