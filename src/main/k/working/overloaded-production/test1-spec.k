// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIFICATION
    imports OVERLOADED-PRODUCTIONS
endmodule

module TEST1-SPEC
    imports VERIFICATION

    rule <k> push overloaded(T:Type, X:Number) ; push overloaded(T:Type, X':Number) ; push overloaded(i32, 1) ; select ; .Pgm => . </k>
         <stack> .Stack => overloaded(T, X') : .Stack </stack>
endmodule
