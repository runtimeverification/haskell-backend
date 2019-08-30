module TEST
    imports DOMAINS

    syntax IValType ::= "i32" | "i64"
    syntax FValType ::= "f32" | "f64"
    syntax AValType ::= IValType | FValType
    syntax Number ::= Int | Float
    syntax IVal ::= "<" IValType ">" Int    [klabel(<_>_)]
    syntax FVal ::= "<" FValType ">" Float  [klabel(<_>_)]
    syntax  Val ::= "<" AValType ">" Number [klabel(<_>_)]
                  | IVal | FVal
    syntax Instr ::= Instr Instr

    syntax PlainInstr ::= IValType "." "const" Int
    syntax Instr ::= PlainInstr
    rule <k> < TYPE:AValType > VAL:Number => .K ... </k>
    rule <k> ITYPE:IValType . const VAL => < ITYPE > VAL ... </k>
    configuration <k> $PGM:Val </k>
endmodule
