module TEST
  import BOOL
  import K-EQUAL

  syntax State ::= St1()
                 | St2()
                 | St3()
                 | St4()

  configuration <k> $PGM:State ~> .K </k>

  rule [AB]: <k> St1() => St2() ... </k>
    requires X ==K St1() andBool X ==K St2()
    // requires no-confusion in the booster SMT solver

  rule [AC]: <k> St1() => St3() ... </k>

  // BTW The :State is necessary. kore-exec crashes with this rule
  // [CD]: <k> (X => d) ~> _Rest </k>
  rule [CD]: <k> (X:State => St4()) ~> _Rest </k>
    requires notBool X ==K St1()
     andBool notBool X ==K St2()
     andBool notBool X ==K St4()
     // X == St3() considering no-junk and no-confusion, unclear without

endmodule
