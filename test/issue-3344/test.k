module TEST
    imports INT
    imports BOOL
    imports SET
    imports SET-SYMBOLIC
    imports K-EQUAL

    configuration <k> $PGM:Step </k>
    syntax Step ::= run ( Set ) | done ( Set )
    rule <k> run(S) => done(S) ... </k>

    rule [set-1]: (SetItem(A) RESTA) -Set SetItem(B) => SetItem(A) (RESTA -Set SetItem(B))
      requires A =/=Int B [simplification]

    rule [set-2]: SetItem(C) -Set (SetItem(D) RESTC) => SetItem(C) -Set RESTC
      requires C =/=Int D [simplification]

    rule [set-3]: SetItem(E) -Set RESTE => SetItem(E)
      requires notBool (E in RESTE) [simplification]

    rule [set-4]: SetItem(F) -Set RESTF => .Set
      requires F in RESTF [simplification]

endmodule
