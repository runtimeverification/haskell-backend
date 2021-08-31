module TEST
  imports BOOL
  imports INT
  imports K-EQUAL

  syntax OpCode ::= "a" | "b" | "c" | "d" | "e" | "f" | "g"

  syntax Bool ::= #changesState(OpCode, Int) [function]

  rule #changesState(a, VALUE) => VALUE =/=Int 0
  rule #changesState(OP,    _) => ( OP ==K b
                                  orBool OP ==K c
                                  )
    requires notBool ( OP ==K a )

endmodule
