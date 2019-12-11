/*

This definition is adapted from the section of wasm-semantics dealing with local
memory. The difficult part is unification with a function in the left-hand side
of the rule: the proof of this rule creates a cyclic substitution which must be
simplified by evaluating the function.

*/
module LOCALS

  imports DOMAINS

  syntax Index ::= Int
  syntax Value ::= "a" | "b"
  syntax Pgm ::= "begin" Index | "end" Value

  configuration
    <T>
      <k> $PGM:Pgm </k>
      <locals> .Map </locals>
    </T>

  syntax Int ::= index( Index ) [function]
  rule index(X:Int) => X

  // This is the difficult rule.
  // The accompanying proof claims that X = index(X), and to complete
  // unification we must evaluated `index(X)`.
  rule
    <k> begin X:Index => end V </k>
    <locals> index(X) |-> V:Value </locals>

endmodule
