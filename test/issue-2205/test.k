module TEST
    imports INT
    configuration <k> init </k>
    syntax KItem ::= "init" | "one" | "two"
    rule <k> init => ?_:Int </k>
    rule <k> 1 => one </k>
    rule <k> 2 => two </k>
endmodule
