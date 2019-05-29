// Copyright (c) 2019 K Team. All Rights Reserved.

module OVERLOADED-PRODUCTIONS-SYNTAX
    imports INT
    imports FLOAT

    syntax Number ::= Int | Float

    syntax IType ::= "i32" | "i64"
    syntax FType ::= "f32" | "f64"
    syntax  Type ::= IType | FType

    syntax Val ::= overloaded(IType, Int)    [klabel(overloadedSymb)]
                 | overloaded(FType, Float)  [klabel(overloadedSymb)]
                 | overloaded( Type, Number) [klabel(overloadedSymb)]
 // -----------------------------------------------------------------

    syntax Stack ::= ".Stack" | Val ":" Stack
 // -----------------------------------------

    syntax Command ::= "push" Val | "select"
 // ----------------------------------------

    syntax Pgm ::= Command ";" Pgm | ".Pgm"
 // ---------------------------------------
endmodule

module OVERLOADED-PRODUCTIONS
    imports OVERLOADED-PRODUCTIONS-SYNTAX

    configuration <k> $PGM:Pgm </k>
                  <stack> .Stack </stack>

    rule <k> .Pgm   => .       ... </k>
    rule <k> C ; P' => C ~> P' ... </k>

    rule <k> push V => . ... </k>
         <stack> S => V : S </stack>

    rule <k> select => . ... </k>
         <stack> overloaded(i32, V) : overloaded(TYPE, N:Number) : overloaded(TYPE, N':Number) : STACK
              => overloaded(TYPE, #if V =/=Int 0 #then N #else N' #fi) : STACK
         </stack>
endmodule
