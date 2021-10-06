module TEST
  imports INT

  syntax Int ::= lookup(Hash) [function, no-evaluators]

  // We use this so that the proof takes a step
  syntax KItem ::= makeLookup(Int)
  rule makeLookup(B) => lookup(#hash(B))

  // -------------------------------------------
  syntax IntList ::= List{Int, ""}

  syntax Bool ::= #rangeUInt(Int) [function, no-evaluators]

  syntax Hash ::= #hash(Int)
                | #hashedLocation( IntList ) [function]

  rule #hashedLocation(       .IntList) => #hash(0)
  rule #hashedLocation(OFFSET .IntList) => #hash(OFFSET)
    requires #rangeUInt(OFFSET)

endmodule
