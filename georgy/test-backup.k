requires "domains.md"

module TEST
    imports INT
    imports SET

    configuration <k> $PGM:Step </k>

    syntax Step ::= run ( Set ) | done ( Set )

    rule [step]: <k> run(S) => done(S) ... </k>

    syntax Bool ::= pred ( Int ) [function, no-evaluators]

    rule [set.diff.empty]: .Set -Set _ => .Set [simplification]
    // rule [set.diff.concat.item]: (SetItem(X) SetItem(Z)) -Set SetItem(Y) => 
    //                         SetItem(X) (SetItem(Z) -Set SetItem(Y))
    rule [set.diff.concat]: (SetItem(X) REST) -Set SetItem(Y) => 
                            SetItem(X) (REST -Set SetItem(Y))
                            [simplification]
    //   requires notBool (X in REST)

      // requires notBool pred(X) andBool pred(Y) 
      // [simplification] // commenting this out makes the proof go through

    // rule [pred.false]: pred(X) => false requires 1 <=Int X andBool X <=Int 9 [simplification]
endmodule

module TEST-SPEC
    imports TEST

    claim <k> run((SetItem(X) REST) -Set SetItem(Y)) => 
              done(SetItem(X) (REST -Set SetItem(Y))) </k>

    // // Works with set.diff.empty, does not withoug -- OK
    // claim <k> run(.Set -Set SetItem(X)) => done(.Set) </k>

    // // Works woth set.diff.concat.item
    // claim <k> run((SetItem(X) SetItem(Z)) -Set SetItem(Y)) => 
    //           done(SetItem(X) (SetItem(Z) -Set SetItem(Y))) </k>

    //   requires notBool (X in Z)
    // claim <k> run(SetItem(X) SetItem(Y)) => done(SetItem(Y) SetItem(X)) </k>
    // claim <k> run(SetItem(Y) -Set SetItem(X)) => done(SetItem(X)) </k> requires X =/=Int Y
endmodule