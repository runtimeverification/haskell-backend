module VERIFICATION
    imports TEST
endmodule

module TEST-1-SPEC
    imports VERIFICATION

    claim a(1 |-> 1 2 |-> 2 3 |-> 3 M:Map) => b
endmodule