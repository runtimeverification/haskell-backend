module TEST

  imports INT
  imports BOOL
  imports SET
  imports K-EQUAL

  syntax Element ::= "a" | "b" | "c"

  syntax Element ::= g(Element) [function, functional]

  rule g(a) => b
  rule g(b) => c
  rule g(c) => a

  syntax Set ::= f(Set) [function, functional]

  rule f(.Set) => .Set
  rule f(SetItem(E:Element) S:Set) => SetItem(g(E)) f(S)

  // for test-1-spec, test-2-spec
  syntax StepSort ::= Set
  syntax    KItem ::= runTest  ( StepSort )
                    | doneTest ( StepSort )
  // ------------------------------------------
  rule runTest( T ) => doneTest( T )

endmodule
