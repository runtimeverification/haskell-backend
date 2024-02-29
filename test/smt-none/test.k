module TEST
imports INT
syntax Type ::= "a" | "b"
syntax Exp ::= Type "=" Type
rule 0 => ?T1:Type = ?T2:Type
rule T = T => .K
endmodule