// Copyright (c) 2019 K Team. All Rights Reserved.
// generated by gen-tests.sh

requires "map-tests.k"

module REMOVE-14-SPEC
    imports MAP-TESTS

    claim <k> remove ( (MAP:Map X:MyId |-> 1) [Y:MyId <- undef] [ Z:MyId ] ) => .K </k> requires Z =/=K Y andBool Z =/=K X

endmodule
