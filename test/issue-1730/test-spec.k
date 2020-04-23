module VERIFICATION
    imports TEST
endmodule

module TEST-SPEC
    imports VERIFICATION
    rule <k> MIN X Y => . ... </k>
         <a> 0 => minInt(X, Y) </a>
endmodule
