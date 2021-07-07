requires "domains.md"

module SET-DIFFERENCE
    imports INT
    imports SET

    configuration <k> $PGM:Step </k>

    syntax Step ::= run ( Set ) | done ( Set )

    rule [step]: <k> run(S) => done(S) ... </k>

    syntax Bool ::= pred ( Int ) [function, no-evaluators]

    rule [set.diff.empty]: .Set -Set _ => .Set [simplification]
    rule [set.diff.concat]: (SetItem(X) REST) -Set SetItem(Y) =>
                            SetItem(X) (REST -Set SetItem(Y))
      requires notBool pred(X) andBool pred(Y)
      [simplification]

    rule [pred.false]: pred(X) => false requires 1 <=Int X andBool X <=Int 9 [simplification]
endmodule