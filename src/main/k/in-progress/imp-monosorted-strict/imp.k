module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= "AInt" Int | "AId" Id
                 | "-" Int
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= "ABool" Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= "ABlock" Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
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

module IMP
  imports IMP-SYNTAX
  imports IMP-STATE
  imports DOMAINS

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .State </state>
                </T>

  syntax KResult ::= Int | Bool

// AExp
  rule <k> AId X:Id => AInt get(S, X) ...</k> <state> S:State </state>
       requires inState(S, X)
  rule AInt I1 / AInt I2 => AInt (I1 /Int I2)  requires I2 =/=Int 0
  rule AInt I1 + AInt I2 => AInt (I1 +Int I2)
  rule - I1 => AInt (0 -Int I1)
// BExp
  rule AInt I1 <= AInt I2 => ABool (I1 <=Int I2)
  rule ! ABool T => ABool (notBool T)
  rule ABool true && B => B
  rule ABool false && _ => ABool false
// Block
  rule ABlock {} => .   [structural]
  rule ABlock {S} => S  [structural]
// Stmt
  rule <k> X = AInt I:Int; => . ...</k> <state> S:State => set(S, X, I) </state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if (ABool true)  S else _ => ABlock S
  rule if (ABool false) _ else S => ABlock S
  rule while (B) S => if (B) {(ABlock S) while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X,Xs => Xs);_ </k> <state> S:State => set(S, X, 0) </state>
    requires notBool (inState(S, X))
  rule int .Ids; S => S  [structural]
endmodule
