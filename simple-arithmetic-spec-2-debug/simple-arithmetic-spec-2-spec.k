requires "kwasm-lemmas.k"

module SIMPLE-ARITHMETIC-SPEC
    imports WASM-TEXT
    imports KWASM-LEMMAS

    // Rules applied:
    //   0 -> 1:  wasm-text.k:103:10-103:74
    //   1 -> 2:  wasm.k:202:10-202:74
    //   2 -> 3:  wasm.k:181:10-183:32

    // From-2: works
    //rule <k> (< ITYPE > X:Int modInt #pow(ITYPE)) => . ... </k>
    //     <valstack> S:ValStack => < ITYPE > (X +Int #pow(ITYPE)) : S </valstack>
    //  requires ((0 -Int #pow1(ITYPE)) <=Int X) andBool (X <Int 0)

    // From-1: doesn't work
    //rule <k> ITYPE:IValType . const X => . ... </k>
    //     <valstack> S:ValStack => < ITYPE > (X +Int #pow(ITYPE)) : S </valstack>
    //  requires ((0 -Int #pow1(ITYPE)) <=Int X) andBool (X <Int 0)

    // Original: doesn't work
    //rule <k> (ITYPE:IValType . const X:Int) => . ... </k>
    //     <valstack> S:ValStack => < ITYPE > (X +Int #pow(ITYPE)) : S </valstack>
    //  requires (#minSigned(ITYPE) <=Int X) andBool (X <Int 0)


endmodule
