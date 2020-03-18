requires "test.k"

module VERIFICATION
    imports TEST
endmodule

module TEST-SPEC
    imports VERIFICATION

    rule <k> #assume false => . </k>

endmodule