requires "test.k"

module TEST-SPEC
    imports TEST

    claim [notInSet]: <k> run( (SetItem(1) -Set (SetItem(2) REST)) REST) => done(SetItem(1) REST) ... </k>
        requires notBool (1 in REST)

    claim [inSet]: <k> run( (SetItem(1) -Set (SetItem(2) REST)) REST) => done(REST) ... </k>
        requires 1 in REST

endmodule