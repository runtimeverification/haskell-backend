module LEM

  import DOMAINS

  syntax PgmState ::= "Start" | "Stop" 

  syntax Int ::= f ( Int ) [function, smtlib((f #0)), functional]

  rule f(1) => f(2) [smt-lemma]
  
  rule f(0) => f(2) [smt-lemma]

  rule Start => Stop requires f(0) ==Int f(1)

endmodule
