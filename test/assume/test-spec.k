requires "test.k"

module VERIFICATION
    imports TEST
endmodule

module TEST-SPEC
    imports VERIFICATION

    claim <k> #assume false => . </k>

endmodule