module VERIFICATION
  imports EITHER

  syntax KItem ::= run ( Either, Int ) | done ( Either )
  rule run(Left(),  _I) => done(Left())
  rule run(Right(), _I) => done(Right())
endmodule

module EITHER-SPEC
  imports VERIFICATION

  claim <k> run(E,I) => done(E) ... </k>
    requires I >Int 0
    ensures P(E,I)
endmodule
