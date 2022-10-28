requires "test.k"

module TEST-SPEC
    imports TEST

    claim [needed]: <k> run( (SetItem(1) -Set (SetItem(2) REST)) REST) => done(SetItem(1) REST) ... </k>
        requires notBool (1 in REST)

endmodule