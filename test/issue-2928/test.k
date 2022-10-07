requires "domains.md"

module TEST
    imports INT
    imports SET
    imports BOOL 

    configuration <k> $PGM:Foo </k>

    syntax Foo ::= run ( Set ) | done ( Set )
 // -----------------------------------------
    rule <k> run(S) => done(S) ... </k>

    syntax Int ::= f ( Int ) [function, no-evaluators]

    rule X ==Int f(X) => false [simplification]
    rule f(X) ==Int X => false [simplification]

    rule X in SetItem(Y) => false requires X =/=Int Y [simplification]

    rule .Set -Set S => .Set [simplification]
    rule (SetItem(X) REST) -Set S => REST -Set S requires X in S [simplification]
    rule (SetItem(X) REST) -Set S => SetItem(X) (REST -Set S) requires notBool (X in S) [simplification, label(toApply)]
    
endmodule