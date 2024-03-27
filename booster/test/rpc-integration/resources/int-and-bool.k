module TEST
  imports INT
  imports BOOL
  imports MAP

// Int map definition from evm-semantics
  syntax Int ::= #lookup ( Map, Int) [symbol(#lookup), function, total, smtlib(lookup)]
//-------------------------------------------------------------------------------------
  rule [#lookup.some]:
       #lookup( (KEY |-> VAL:Int) _M, KEY) => VAL
  rule [#lookup.none]:
       #lookup( M, KEY) => 0                  requires notBool KEY in_keys(M)
  rule [#lookup.notInt]:
       #lookup( (KEY |-> VAL) _M, KEY) => VAL requires notBool isInt(VAL)
//-------------------------------------------------------------------------------------

endmodule
