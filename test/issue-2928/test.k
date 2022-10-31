requires "domains.md"

module TEST
    imports INT
    imports SET
    imports SET-SYMBOLIC
    imports BOOL
    imports K-EQUAL

    configuration <k> $PGM:Foo </k>

    syntax Foo ::= run ( Set ) | done ( Set )
 // -----------------------------------------
    rule <k> run(S) => done(S) ... </k>

    syntax Int ::= f ( Int ) [function, no-evaluators]

    rule X ==Int f(X) => false [simplification]
    rule f(X) ==Int X => false [simplification]

    rule X in SetItem(Y) => false requires X =/=Int Y [simplification]

    rule SetItem(X) |Set SetItem(Y) => SetItem(X) SetItem(Y)
      requires X =/=K Y [simplification]

endmodule