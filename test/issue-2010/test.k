module TEST
    imports BOOL
    imports INT

    syntax MaybeInt ::= "Some" Int
                      | "None"
    syntax MaybeInt ::= f() [function, functional, no-evaluators]

    configuration <k> f() </k>

    rule <k> None => true ... </k>
    rule <k> Some I => I ... </k>
endmodule