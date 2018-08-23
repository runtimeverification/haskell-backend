require "../lib/state.k"

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

  syntax KResult ::= Int | Bool

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
endmodule

module IMP-STATE
  imports IMP-SYNTAX
  imports STATE-BASIC
  syntax Id ::= "sum" [token]
              | "n" [token]

  syntax StateKey ::= Id
  syntax StateValue ::= Int

  rule get((n |-> _:StateValue) S:State, sum) => get(S, sum)
  rule get((sum |-> _:StateValue) S:State, n) => get(S, n)
  rule set((n |-> V:StateValue) S:State, sum, V':StateValue) => (n |-> V:StateValue) set(S, sum, V')
  rule set((sum |-> V:StateValue) S:State, n, V':StateValue) => (sum |-> V:StateValue) set(S, n, V')
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
  rule <k> X:Id => get(S, X) ...</k> <state> S:State </state>
       requires inState(S, X)
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 +' I2 => I1 +Int I2
  rule - I1 => 0 -Int I1
// BExp
  rule I1 <=' I2 => I1 <=Int I2
  rule !' T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X =' I:Int; => . ...</k> <state> S:State => set(S, X, I) </state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if' (true)  S else _ => S
  rule if' (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
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
      inj{SortStateValue{},SortKItem{}}(inj{SortInt{},SortStateValue{}}(T:SortInt{}))
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