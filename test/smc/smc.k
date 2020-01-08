module SMC-SYNTAX
  imports DOMAINS-SYNTAX

  syntax AExp  ::= Int | Id
                 | "-" Int                    [format(%1%2)]
                 | AExp "/" AExp              [left, color(pink)]
                 > AExp "+" AExp              [left, color(pink)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [latex({#1}\leq{#2}), color(pink)]
                 | "!" BExp                   [color(pink)]
                 > BExp "&&" BExp             [left, color(pink)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"               [format(%1%i%n%2%d%n%3)]
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [color(pink), format(%1 %2 %3%4)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [colors(yellow, white, white, yellow), format(%1 %2%3%4 %5 %6 %7)]
                 | "while" "(" BExp ")" Block [colors(yellow,white,white), format(%1 %2%3%4 %5)]
                 > Stmt Stmt                  [left, format(%1%n%2)]

  syntax Pgm ::= "int" Ids ";" Stmt           [format(%1 %2%3%n%4), colors(yellow,pink)]
  syntax Ids ::= List{Id,","} [format(%1%2 %3)]
endmodule

module SMC
  imports SMC-SYNTAX
  imports DOMAINS

  syntax KItem ::= "+" | "-" | "/" | "<=" | "!" | "&&" BExp | Id "=" | choice(Block, Block) | "STUCK"

  syntax Val ::= Int | Bool

  syntax ValStack ::= ".ValStack" | Val ":" ValStack

  syntax Int ::= stackSize(ValStack) [function, functional, smtlib(stackSize)]
  rule stackSize(.ValStack) => 0
  rule stackSize(V:Val : S:ValStack) => 1 +Int stackSize(S)

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <mem color="red"> .Map </mem>
                  <stack color="blue"> .ValStack </stack>
                </T>

  rule <k> X:Id => I ...</k> <mem>... X |-> I ...</mem>
  rule <k> I:Int => . ...</k> <stack> S:ValStack => I : S </stack>
    requires stackSize(S) <Int 8
  rule <k> I:Int => STUCK ...</k> <stack> S:ValStack => S </stack>
    requires stackSize(S) >=Int 8


  rule E1:AExp / E2:AExp => E1 ~> E2 ~> /
  rule <k> / => . ...</k>
       <stack> I2:Int : I1:Int : S:ValStack => I1 /Int I2 : S </stack>
  requires I2 =/=Int 0

  rule E1:AExp + E2:AExp => E1 ~> E2 ~> +
  rule <k> + => . ...</k>
       <stack> I2:Int : I1:Int : S:ValStack => I1 +Int I2 : S </stack>

  rule - I:Int => I ~> -
  rule <k> - => . ...</k>
       <stack> I:Int : S:ValStack => 0 -Int I : S </stack>

  rule E1:AExp <= E2:AExp => E1 ~> E2 ~> <=
  rule <k> <= => . ...</k>
       <stack> I2:Int : I1:Int : S:ValStack => I1 <=Int I2 : S </stack>

  rule ! E:BExp => E ~> !
  rule <k> ! => . ...</k>
       <stack> B:Bool : S:ValStack => notBool(B) : S </stack>

  rule E1:BExp && E2:BExp => E1 ~> && E2
  rule <k> && E => . ...</k>
       <stack> false : S:ValStack => false : S </stack>
  rule <k> && E => E ...</k>
       <stack> true : S:ValStack => S </stack>

  rule {} => .   [structural]
  rule {S} => S  [structural]

  rule X:Id = E:AExp ; => E ~> X =
  rule <k> X = => . ...</k>
       <mem>... X |-> (_ => I) ...</mem>
       <stack> I:Int : S:ValStack => S </stack>

  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]

  rule if (B:BExp) S1:Block else S2:Block  => B ~> choice(S1,S2)
  rule <k> choice(Bl,_) => Bl ...</k> <stack> true : S:ValStack => S </stack>
  rule <k> choice(_,Bl) => Bl ...</k> <stack> false : S:ValStack => S </stack>

  rule while (B:BExp) Bl:Block => if (B) { Bl while(B) Bl } else {}

  rule <k> int (X,Xs => Xs);_ </k> <mem> Rho:Map (.Map => X|->0) </mem>
    requires notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]
endmodule
