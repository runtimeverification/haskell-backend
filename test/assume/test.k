requires "domains.md"

module TEST
    imports DOMAINS

    configuration <k> $PGM:KItem </k>

    syntax KItem ::= "#assume" Bool
    rule <k> #assume B => .K ... </k> ensures B

endmodule
