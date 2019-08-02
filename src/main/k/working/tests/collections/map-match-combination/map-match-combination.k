module MAP-MATCH-COMBINATION

    imports DOMAINS

    syntax Int ::= sum ( Map , Int )            [function]

    syntax Thing ::= "start"

    rule start => sum( 0 |-> 1 1 |-> 20 2 |-> 320, 1)

    rule sum(M, END)           => 0
        requires END <Int 0
    rule sum(M, END)           => sum(M, END -Int 1)
        requires (END >=Int 0) andBool notBool END in_keys(M)
    rule sum(END |-> W M, END) => sum(M, END -Int 1) +Int W
        requires (END >=Int 0)

endmodule