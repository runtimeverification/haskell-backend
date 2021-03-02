// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module VERIFICATION
    imports MAP-TESTS

endmodule

module REMOVE-12-SPEC
    imports VERIFICATION

    claim <k> remove ( (MAP:Map X:MyId |-> 1) [Y:MyId <- undef] [ Z:MyId ] ) => . </k> requires Z ==K Y

endmodule
