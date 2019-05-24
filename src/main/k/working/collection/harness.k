module HARNESS

  imports DOMAINS

  // Test harness

  syntax Cmd ::= "eval" KItem | "end"

  syntax KItem ::= "a" [token]
                 | "b" [token]
                 | "c" [token]

  configuration
    <T>
      <k> $PGM:Cmd </k>
    </T>

  syntax Cmd ::= "test-set-idem"
  rule <k> test-set-idem => end </k>
    requires (SetItem(a) SetItem(a)) ==K SetItem(a)

  syntax Cmd ::= "test-map-idem"
  rule <k> test-map-idem => end </k>
    requires (a |-> b  a |-> b) ==K (a |-> b)

endmodule