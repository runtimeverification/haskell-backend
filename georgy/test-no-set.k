requires "domains.md"

module TEST-NO-SET
    imports INT

    configuration <k> $PGM:Step </k>

    syntax Step ::= run ( Int ) | done ( Int )
    rule [step]: <k> run(S) => done(S) ... </k>

    syntax Bool ::= pred ( Int ) [function, no-evaluators]
    syntax Int ::= f (Int, Int) [function, no-evaluators]

    rule [pred.false]: pred(X) => false requires 1 <=Int X andBool X <=Int 9 [simplification]
    rule [f.rule]: f(X, Y) => 4 requires pred(X) andBool notBool pred(Y) [simplification]
endmodule

module TEST-SPEC
    imports TEST-NO-SET

    claim <k> run(f(X, 7)) => done(4) ... </k> requires pred(X)
endmodule