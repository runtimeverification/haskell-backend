requires "either.k"

module EITHER-SPEC
  imports EITHER

  claim <k> run(E,I) => done(E) ... </k>
    requires I >Int 0
    ensures P(E,I)
endmodule
