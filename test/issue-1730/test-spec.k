requires "test.k"

module VERIFICATION
    imports TEST
endmodule

module TEST-SPEC
    imports VERIFICATION
    claim <k> MIN X Y => . ... </k>
         <a> 0 => minInt(X, Y) </a>
endmodule
