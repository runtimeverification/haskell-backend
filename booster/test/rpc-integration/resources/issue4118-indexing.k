module TEST
  imports LIST
  imports MAP
  imports SET

  configuration
      <k> $PGM:Abcd ~> .K </k>

  syntax KItem ::= "Done"        [symbol(Done)]

  syntax Abcd ::= "A" | "B"
                | Cons ( Abcd ) [symbol(Cons)]
                | f ( Abcd )    [function, total, symbol(f)]

  rule f(A) => f(B) // index TopFun "f"
  rule f(B) => A    // index TopFun "f"

  rule [Vrule]: // index TopVal "A"
    <k> A => Done ... </k>

  rule [consrule]: // index TopCon "Cons"
    <k> Cons(I) => f(I) ... </k>

  rule [varrule]: // index ***
    <k> _X:Abcd => B ... </k> [owise]

// Bug Demonstrator #4118:
// Cons(B) =rewrite=> f(B) =eval=> A =rewrite=> Done    correct
//                       \
//                        \=rewrite=> B [owise]    should not apply!

endmodule
