requires "test.k"

module TEST-SPEC
    imports TEST
    claim <k> MIN X Y => .K ... </k>
         <a> 0 => minInt(X, Y) </a>
endmodule
