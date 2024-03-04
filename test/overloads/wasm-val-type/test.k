module TEST
    imports INT
    imports FLOAT

    syntax IValType ::= "i32" | "i64"
    syntax FValType ::= "f32" | "f64"
    syntax AValType ::= IValType | FValType
    syntax Number ::= Int | Float
    syntax IVal ::= "<" IValType ">" Int    [overload(<_>_)]
    syntax FVal ::= "<" FValType ">" Float  [overload(<_>_)]
    syntax  Val ::= "<" AValType ">" Number [overload(<_>_)]
                  | IVal | FVal
    syntax Instr ::= Instr Instr

    syntax PlainInstr ::= IValType "." "const" Int
    syntax Instr ::= PlainInstr
    rule <k> < TYPE:AValType > VAL:Number => .K ... </k>
    rule <k> ITYPE:IValType . const VAL => < ITYPE > VAL ... </k>
    configuration <k> $PGM:Number </k>

    syntax Number ::= extractNumber(Val) [function]
    rule extractNumber( < TYPE > N:Number ) => N
endmodule
