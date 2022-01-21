requires "test.k"

module VERIFICATION
    imports TEST
    imports INT-SYNTAX

endmodule

module TEST-SPEC
    imports VERIFICATION

    claim <k> foo => 1234 </k> 

endmodule
