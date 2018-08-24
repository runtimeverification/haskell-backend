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

module STATE-API
  imports IMP-SYNTAX

  syntax Assignment
    ::= Id "|->" Int

  syntax State
    ::= ".State" | Assignment State

  syntax State ::= set(State, Id, Int) [function]

  syntax Bool ::= inState(State, Id) [function]

  syntax Int ::= get(State, Id) [function, partial]
endmodule

module STATE-BASIC
  imports STATE-API
  rule set(.State, K:Id, V:Int) => (K |-> V) .State
  rule set((K:Id |-> _:Int) S:State, K:Id, V:Int)
       => (K |-> V) S

  rule inState(.State, _) => false
  rule inState((K:Id |-> _:Int) S:State, K:Id) => true

  rule get((K:Id |-> V:Int) S:State, K:Id) => V
endmodule


module IMP-STATE
  imports IMP-SYNTAX
  imports STATE-BASIC
  syntax Id ::= "sum" [token]
              | "n" [token]

  rule get((n |-> _:Int) S:State, sum) => get(S, sum)
  rule get((sum |-> _:Int) S:State, n) => get(S, n)
  rule set((n |-> V:Int) S:State, sum, V':Int) => (n |-> V:Int) set(S, sum, V')
  rule set((sum |-> V:Int) S:State, n, V':Int) => (sum |-> V:Int) set(S, n, V')
endmodule

module IMP
  imports IMP-SYNTAX
  imports IMP-STRICT
  imports IMP-STATE
  imports DOMAINS

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

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule

/*

  axiom{} \and{SortTCell{}} (
    \top{SortTCell{}}(), \and{SortTCell{}} (
    \top{SortTCell{}}(), \rewrites{SortTCell{}}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(
      inj{SortAExp{},SortKItem{}}(inj{SortId{},SortAExp{}}(T:SortId{}))
         ,VarDotVar1:SortK{})),VarDotVar0:SortStateCell{}),Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(
      inj{SortId{},SortKItem{}}(T:SortId{})
      ,VarDotVar1:SortK{})),VarDotVar0:SortStateCell{}))))
  []

  axiom{} \and{SortTCell{}} (
    \top{SortTCell{}}(), \and{SortTCell{}} (
    \top{SortTCell{}}(), \rewrites{SortTCell{}}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(
      inj{SortAExp{},SortKItem{}}(inj{SortInt{},SortAExp{}}(T:SortInt{}))
         ,VarDotVar1:SortK{})),VarDotVar0:SortStateCell{}),Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(
      inj{SortInt{},SortKItem{}}(T:SortInt{})
      ,VarDotVar1:SortK{})),VarDotVar0:SortStateCell{}))))
  []

  axiom{} \and{SortTCell{}} (
    \top{SortTCell{}}(), \and{SortTCell{}} (
    \top{SortTCell{}}(), \rewrites{SortTCell{}}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(
      inj{SortInt{},SortKItem{}}(inj{SortInt{},SortInt{}}(T:SortInt{}))
         ,VarDotVar1:SortK{})),VarDotVar0:SortStateCell{}),Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(
      inj{SortInt{},SortKItem{}}(T:SortInt{})
      ,VarDotVar1:SortK{})),VarDotVar0:SortStateCell{}))))
  []

  axiom{} \and{SortTCell{}} (
    \top{SortTCell{}}(), \and{SortTCell{}} (
    \top{SortTCell{}}(), \rewrites{SortTCell{}}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(
      inj{SortStmt{},SortKItem{}}(inj{SortBlock{},SortStmt{}}(T:SortBlock{}))
         ,VarDotVar1:SortK{})),VarDotVar0:SortStateCell{}),Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(
      inj{SortBlock{},SortKItem{}}(T:SortBlock{})
      ,VarDotVar1:SortK{})),VarDotVar0:SortStateCell{}))))
  []

*/