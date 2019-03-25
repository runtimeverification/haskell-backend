// This is IMP with user-defined heating-cooling rules using Map as a drop-in
// replacement for State. Notably, it does not use unification on Map.

module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | Id
                 | "-" Int
                 | AExp "/" AExp              [left/*, strict*/]
                 > AExp "+" AExp              [left/*, strict*/]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [/*seqstrict,*/ latex({#1}\leq{#2})]
                 | "!" BExp                   /*[strict]*/
                 > BExp "&&" BExp             [left/*, strict(1)*/]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            /*[strict(2)]*/
                 | "if" "(" BExp ")"
                   Block "else" Block         /*[strict(1)]*/
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule

module IMP-STRICT
  imports IMP-SYNTAX

  syntax KItem ::= "if" "(" "HOLE" ")"
                   Block "else" Block         /*[strict(1)]*/
                 | "if'" "(" Bool ")"
                   Block "else" Block         /*[strict(1)]*/
                 | "HOLE" "<=" AExp
                 | Int "<=" "HOLE"
                 | Int "<='" Int
                 | "!" "HOLE"
                 | "!'" Bool
                 | Id "=" "HOLE" ";"
                 | Id "='" Int ";"
                 | "HOLE" "+" AExp
                 | Int "+" "HOLE"
                 | Int "+'" Int
                 | "HOLE" "/" AExp
                 | Int "/" "HOLE"
                 | Int "/'" Int
                 | "HOLE" "&&" BExp
                 | Bool "&&'" BExp
  rule if (B:BExp) B1:Block else B2:Block => B ~> if (HOLE) B1 else B2
  rule T:Bool ~> if (HOLE) B1 else B2 => if' (T) B1:Block else B2:Block
  rule ! B:BExp => B ~> ! HOLE
  rule T:Bool ~> ! HOLE => !' T
  rule A1:AExp <= A2:AExp => A1 ~> HOLE <= A2
  rule I1:Int ~> HOLE <= A2:AExp => A2 ~> I1 <= HOLE
  rule I2:Int ~> I1:Int <= HOLE => I1 <=' I2
  rule X:Id = A:AExp ; => A ~> X = HOLE ;
  rule I:Int ~> X:Id = HOLE ; => X =' I ;
  rule A1:AExp + A2:AExp => A1 ~> HOLE + A2
  rule I1:Int ~> HOLE + A2:AExp => A2 ~> I1 + HOLE
  rule I2:Int ~> I1:Int + HOLE => I1 +' I2
  rule A1:AExp / A2:AExp => A1 ~> HOLE / A2
  rule I1:Int ~> HOLE / A2:AExp => A2 ~> I1 / HOLE
  rule I2:Int ~> I1:Int / HOLE => I1 /' I2
  rule A1:BExp && A2:BExp => A1 ~> HOLE && A2
  rule T1:Bool ~> HOLE && A2:BExp =>  T1 &&' A2
endmodule


module SYMBOLIC-INT
  imports IMP-SYNTAX
  syntax AExp ::= "symInt"
  rule symInt => ?I:Int
endmodule

module IMP
  imports IMP-SYNTAX
  imports IMP-STRICT
  imports DOMAINS
  imports SYMBOLIC-INT

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>

// AExp
  rule <k> X:Id => I ...</k> <state> ... X |-> I ... </state>
  rule I1 /' I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 +' I2 => I1 +Int I2
  rule - I1 => 0 -Int I1
// BExp
  rule I1 <=' I2 => I1 <=Int I2
  rule !' T => notBool T
  rule true &&' B => B
  rule false &&' _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X =' I:Int; => . ...</k> <state> ... X |-> (_ => I) ... </state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if' (true)  S else _ => S
  rule if' (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X,Xs => Xs);_ </k> <state> (.Map => X |-> 0) M:Map </state>
    requires notBool (X in_keys(M))
  rule int .Ids; S => S  [structural]

endmodule