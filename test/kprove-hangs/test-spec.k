module VERIFICATION
    imports TEST

endmodule

module TEST-SPEC
    imports VERIFICATION

    claim <k> (a ~> _ => .) ... </k>

endmodule
