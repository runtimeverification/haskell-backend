module NO-EVALUATOR
  imports INT

  syntax Foo ::= Foo ( Int )
               | f ( Int ) [function, no-evaluators] // a non-concrete value

  rule Foo ( X ) => f ( X )
endmodule
