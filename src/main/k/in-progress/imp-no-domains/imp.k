require "../lib/adomains.k"
require "../lib/astate.k"

module IMP-SYNTAX
  imports AID-SYNTAX
  imports ABOOL-SYNTAX
  imports AINT-SYNTAX
  syntax AExp  ::= AId | AInt
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= ABool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | AId "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= Stmt
endmodule

module IMP
  imports IMP-SYNTAX
  imports AINT
  imports ASTATE

  syntax KResult ::= AInt | ABool
  syntax StateKey ::= AId
  syntax StateValue ::= AInt

  configuration
    <T> <k> $PGM:Pgm </k> <state> .State </state> </T>

  rule S1:Stmt S2:Stmt => S1 ~> S2
  
  rule <k> X:AId = I:AInt ; => .K ...</k> <state> S:State => set(S, X, I) </state>

  rule while (C:BExp) S:Block => if (C) { S while (C) S } else {}

  rule <k> X:AId => get(S,X) ...</k> <state> S:State </state>

  rule I1:AInt <= I2:AInt => I1 <=AInt I2

  rule if (One) S:Block else _ => S

  rule if (Zero) _ else S:Block => S

  rule { S:Stmt } => S

  rule I1:AInt + I2:AInt => I1 +AInt I2

  rule {} => .K
endmodule
