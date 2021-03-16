module TEST
    imports INT
    syntax FOO ::= "foo"
    configuration <k> foo ~> $PGM:Int </k>
    rule <k> foo => #Bottom ... </k>
endmodule