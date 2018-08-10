require "domains.k"

module ABOOL-SYNTAX
  syntax ABool ::= "Zero" | "One"
endmodule

module AINT-SYNTAX
  imports ABOOL-SYNTAX
  syntax AInt ::=  ".AInt" | ABool AInt | "(" AInt ")" [bracket]
endmodule

module AINT
  import AINT-SYNTAX
  import ABOOL-SYNTAX

  syntax AInt
    ::= AInt "+AInt" AInt [function]
      | addWithCarry(AInt, AInt, ABool) [function]

  rule I1:AInt +AInt I2:AInt => addWithCarry(I1, I2, Zero)

  rule addWithCarry(.AInt, I:AInt, Zero) => I
  rule addWithCarry(.AInt, I:AInt, One) => addWithCarry(One .AInt, I, Zero)
  rule addWithCarry(I:AInt, .AInt, Zero) => I
  rule addWithCarry(I:AInt, .AInt, One) => addWithCarry(I, One .AInt, Zero)
  
  rule addWithCarry(Zero I1:AInt, B:ABool I2:AInt, Zero) => B addWithCarry(I1, I2, Zero)
  rule addWithCarry(B:ABool I1:AInt, Zero I2:AInt, Zero) => B addWithCarry(I1, I2, Zero)
  rule addWithCarry(Zero I1:AInt, Zero I2:AInt, B:ABool) => B addWithCarry(I1, I2, Zero)
  rule addWithCarry(One I1:AInt, One I2:AInt, B:ABool) => B addWithCarry(I1, I2, One)
  rule addWithCarry(One I1:AInt, B:ABool I2:AInt, One) => B addWithCarry(I1, I2, One)
  rule addWithCarry(B:ABool I1:AInt, One I2:AInt, One) => B addWithCarry(I1, I2, One)

  syntax ABool
    ::= AInt "<=AInt" AInt [function]
      | leqWithCarry(AInt, AInt, ABool) [function]

  rule I1:AInt <=AInt I2:AInt => leqWithCarry(I1, I2, One)

  rule leqWithCarry(.AInt, _, One) => One
  rule leqWithCarry(.AInt, Zero I:AInt => I, Zero)
  rule leqWithCarry(.AInt, One I:AInt, _) => One
  rule leqWithCarry(.AInt, .AInt, B:ABool) => B
  rule leqWithCarry(_, .AInt, Zero) => Zero
  rule leqWithCarry(Zero I:AInt => I, .AInt, One)
  rule leqWithCarry(One I:AInt, .AInt, _) => Zero
  rule leqWithCarry(Zero I1:AInt, Zero I2:AInt, R:ABool) => leqWithCarry(I1, I2, R)
  rule leqWithCarry(One I1:AInt, Zero I2:AInt, _:ABool) => leqWithCarry(I1, I2, Zero)
  rule leqWithCarry(Zero I1:AInt, One I2:AInt, _:ABool) => leqWithCarry(I1, I2, One)
  rule leqWithCarry(One I1:AInt, One I2:AInt, R:ABool) => leqWithCarry(I1, I2, R)
endmodule

module AID-SYNTAX
  syntax AId
    ::= "n"
      | "i"
      | "sum"
endmodule

module AID
  imports AID-SYNTAX
  imports BOOL

  syntax Bool ::= AId "=/=AId" AId [function]

  rule n =/=AId n => false
  rule n =/=AId i => true
  rule n =/=AId sum => true

  rule i =/=AId n => true
  rule i =/=AId i => false
  rule i =/=AId sum => true

  rule sum =/=AId n => true
  rule sum =/=AId i => true
  rule sum =/=AId sum => false
endmodule

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

module STATE
  imports AID
  imports AINT-SYNTAX

  syntax Assignment
    ::= AId "|->" AInt

  syntax State
    ::= ".State" | Assignment State
      | set(State, AId, AInt) [function]

  syntax AInt ::= get(State, AId) [function]

  rule set(.State, X:AId, I:AInt) => (X |-> I) .State

  rule set((X:AId |-> _:AInt) S:State, X, I:AInt) => (X |-> I) S
  rule set((X:AId |-> J:AInt) S:State, Y:AId, I:AInt) => (X |-> J) set(S, Y, I)
    requires X =/=AId Y

  rule get(.State, X:AId) => .AInt

  rule get((X:AId |-> I:AInt) S:State, X) => I
  rule get((X:AId |-> _:AInt) S:State, Y:AId) => get(S, Y)
    requires X =/=AId Y
endmodule

module IMP
  imports IMP-SYNTAX
  imports AINT
  imports STATE

  syntax KResult ::= AInt | ABool

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
