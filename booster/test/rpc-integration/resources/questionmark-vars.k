module QUESTIONMARK-VARS
  syntax State ::= "a"
                 | "b"
                 | ".State"

  syntax KItem ::= "#setAStateSymbolic" [klabel(setAStateSymbolic)]
  syntax KItem ::= "#setBStateSymbolic" [klabel(setBStateSymbolic)]

  syntax Bool ::= condition(State) [function, total, no-evaluators]

  configuration <k> $PGM:KItem ~> .K </k>
                <a-state> .State     </a-state>
                <b-state> .State     </b-state>

  rule [make-a-state-symbolic]:
       <k> #setAStateSymbolic => . ... </k>
       <a-state> _ => ?X               </a-state>
       ensures condition(?X)

  rule [make-b-state-symbolic]:
       <k> #setBStateSymbolic => . ... </k>
       <b-state> _ => ?X              </b-state>
       ensures condition(?X)

endmodule