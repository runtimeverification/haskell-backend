requires "test.k"

module VERIFICATION
    imports TEST
endmodule

module TEST-SPEC
    imports VERIFICATION

    claim <k> ITYPE:IValType . const X:Int => . ... </k>

endmodule
