module MAP-LOOKUP

  imports DOMAINS

  syntax Int ::= #lookup ( Map , Int ) [function]

  // -----------------------------------------------
  rule #lookup( (KEY |-> VAL) M, KEY ) => VAL
  rule #lookup(               M, KEY ) => 0 requires notBool KEY in_keys(M)

  syntax Val ::= "x" | "y" | "z"
               | "success" | "ready" | get(Int)
               | "test1" | "test2"

  configuration
    <T>
      <k> $PGM:Val </k>
      <a> .Map </a>
    </T>


  rule <k> get(I:Int) => #lookup(M, I) ...</k>
       <a> M:Map </a>

  // --- some initial values ---

  // PASS
  rule
    <k> test1 => get(3) ... </k>
    <a> .Map => 3 |-> success </a>

  rule
    <k> test2 => get(3) ... </k>
    <a> .Map </a>

endmodule
