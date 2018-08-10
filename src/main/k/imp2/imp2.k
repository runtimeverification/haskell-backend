module IMP2-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | Id
                 | "-" Int
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}  
endmodule

module STATE
  imports K-EQUAL

  syntax StateKey
  syntax StateValue
  syntax State ::= ".State"
                 | Set(State, StateKey, StateValue)
                 | set(State, StateKey, StateValue) [function]

  rule set(.State, K:StateKey, V:StateValue) => Set(.State, K, V)
  rule set(Set(S:State, K:StateKey, _:StateValue), K:StateKey, V:StateValue)
       => Set(S, K, V)
  rule set(Set(S:State, K:StateKey, V:StateValue), K':StateKey, V':StateValue)
       => Set(set(S, K', V'), K, V)
       requires K =/=K K'
  
  syntax Bool ::= inState(State, StateKey) [function]
  rule inState(.State, _) => false
  rule inState(Set(S:State, K:StateKey, _), K:StateKey) => true
  rule inState(Set(S:State, K:StateKey, _), K':StateKey) => inState(S, K')
       requires K =/=K K'
 
  syntax StateValue ::= get(State, StateKey) [function, partial]
  rule get(Set(S:State, K:StateKey, V:StateValue), K:StateKey) => V
  rule get(Set(S:State, K:StateKey, _), K':StateKey) => get(S, K')
       requires K =/=K K'
 endmodule

module IMP2
  imports IMP2-SYNTAX
  imports DOMAINS
  imports STATE

  syntax KResult ::= Int | Bool

  syntax StateKey ::= Id
  syntax StateValue ::= Int

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .State </state>
                </T>

// AExp
  rule <k> X:Id => get(S, X) ...</k> <state> S:State </state>
       requires inState(S, X)
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I1 => 0 -Int I1
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X = I:Int; => . ...</k> <state> S:State => set(S, X, I) </state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X,Xs => Xs);_ </k> <state> S:State => set(S, X, 0) </state>
    requires notBool (inState(S, X))
  rule int .Ids; S => S  [structural]

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule
