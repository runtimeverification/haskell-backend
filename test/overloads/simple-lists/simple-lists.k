module SIMPLE-LISTS
    imports BOOL
    syntax EmptyStmt
 // ----------------

    syntax Instr ::= EmptyStmt
    syntax Defn  ::= EmptyStmt
    syntax Stmt  ::= Instr | Defn
 // -----------------------------

    syntax EmptyStmts ::= List{EmptyStmt , ""} [klabel(listStmt)]
    syntax Instrs     ::= List{Instr     , ""} [klabel(listStmt)]
    syntax Defns      ::= List{Defn      , ""} [klabel(listStmt)]
    syntax Stmts      ::= List{Stmt      , ""} [klabel(listStmt)]
 // -------------------------------------------------------------

    syntax Instrs ::= EmptyStmts
    syntax Defns  ::= EmptyStmts
    syntax Stmts  ::= Instrs | Defns

    syntax Instr ::= "i1" | "i2"
    syntax Defn ::= "d1" | "d2"

    rule d1 d2 => i1 i2

    syntax EmptyStmt ::= "e"

    syntax Instr ::= mkEmptyInstr() [function, total]
    rule mkEmptyInstr() => e

    rule D:Defn Ds:Defns => D ~> Ds
    rule e => .

    rule .Stmts => .

    configuration <k> $PGM:Stmts </k>
endmodule