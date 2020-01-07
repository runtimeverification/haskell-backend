module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= "AInt" Int | "AId" Id
                 | "-" Int
                 | AExp "/" AExp              [left/*, strict*/]
                 > AExp "+" AExp              [left/*, strict*/]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= "ABool" Bool
                 | AExp "<=" AExp             [/*seqstrict,*/ latex({#1}\leq{#2})]
                 | "!" BExp                   /*[strict]*/
                 > BExp "&&" BExp             [left/*, strict(1)*/]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= "ABlock" Block
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
  rule ABool T:Bool ~> if (HOLE) B1 else B2 => if' (T) B1:Block else B2:Block
  rule ! B:BExp => B ~> ! HOLE
  rule ABool T:Bool ~> ! HOLE => !' T
  rule A1:AExp <= A2:AExp => A1 ~> HOLE <= A2
  rule AInt I1:Int ~> HOLE <= A2:AExp => A2 ~> I1 <= HOLE
  rule AInt I2:Int ~> I1:Int <= HOLE => I1 <=' I2
  rule X:Id = A:AExp ; => A ~> X = HOLE ;
  rule AInt I:Int ~> X:Id = HOLE ; => X =' I ;
  rule A1:AExp + A2:AExp => A1 ~> HOLE + A2
  rule AInt I1:Int ~> HOLE + A2:AExp => A2 ~> I1 + HOLE
  rule AInt I2:Int ~> I1:Int + HOLE => I1 +' I2
  rule A1:AExp / A2:AExp => A1 ~> HOLE / A2
  rule AInt I1:Int ~> HOLE / A2:AExp => A2 ~> I1 / HOLE
  rule AInt I2:Int ~> I1:Int / HOLE => I1 /' I2
  rule A1:BExp && A2:BExp => A1 ~> HOLE && A2
  rule ABool T1:Bool ~> HOLE && A2:BExp =>  T1 &&' A2
endmodule

module IMP-STATE
  imports IMP-SYNTAX

  syntax Assignment
    ::= Id "|->" Int

  syntax State
    ::= ".State" | Assignment State

  syntax State ::= set(State, Id, Int) [function]

  rule set(.State, K:Id, V:Int) => (K |-> V) .State
  rule set((K:Id |-> _:Int) S:State, K:Id, V:Int)
       => (K |-> V) S
  rule set((X:Id |-> V:Int) S:State, Y:Id, V':Int) => (X |-> V) set(S, Y, V')
       requires X =/=K Y

  syntax Bool ::= inState(State, Id) [function]

  rule inState(.State, _) => false
  rule inState((K:Id |-> _:Int) S:State, K:Id) => true
  rule inState((K:Id |-> _:Int) S:State, K':Id) => inState(S, K')
       requires K =/=K K'

  syntax Int ::= get(State, Id) [function, partial]

  rule get((K:Id |-> V:Int) S:State, K:Id) => V
  rule get((X:Id |-> _:Int) S:State, Y:Id) => get(S, Y)
       requires X =/=K Y

endmodule

module SYMBOLIC-INT
  imports IMP-SYNTAX
  syntax AExp ::= "symInt"
  rule symInt => AInt ?I:Int
endmodule

module IMP
  imports IMP-SYNTAX
  imports IMP-STRICT
  imports IMP-STATE
  imports DOMAINS

  imports SYMBOLIC-INT

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .State </state>
                </T>

// AExp
  rule <k> AId X:Id => AInt get(S, X) ...</k> <state> S:State </state>
       requires inState(S, X)
  rule I1 /' I2 => AInt (I1 /Int I2)  requires I2 =/=Int 0
  rule I1 +' I2 => AInt (I1 +Int I2)
  rule - I1 => AInt (0 -Int I1)
// BExp
  rule I1 <=' I2 => ABool (I1 <=Int I2)
  rule !' T => ABool (notBool T)
  rule true &&' B => B
  rule false &&' _ => ABool false
// Block
  rule ABlock {} => .   [structural]
  rule ABlock {S} => S  [structural]
// Stmt
  rule <k> X =' I:Int; => . ...</k> <state> S:State => set(S, X, I) </state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if' (true)  S else _ => ABlock S
  rule if' (false) _ else S => ABlock S
  rule while (B) S => if (B) {(ABlock S) while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X,Xs => Xs);_ </k> <state> S:State => set(S, X, 0) </state>
    requires notBool (inState(S, X))
  rule int .Ids; S => S  [structural]
endmodule
