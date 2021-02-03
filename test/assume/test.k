requires "domains.md"

module TEST
    imports DOMAINS

    configuration <k> $PGM:KItem </k>

    syntax KItem ::= "#assume" Bool
    rule <k> #assume B => . ... </k> ensures B

endmodule
