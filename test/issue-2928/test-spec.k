module TEST-SPEC
    imports TEST

    claim <k> run(SetItem(X) |Set SetItem(f(X))) => done(SetItem(X) SetItem(f(X))) ... </k>

endmodule