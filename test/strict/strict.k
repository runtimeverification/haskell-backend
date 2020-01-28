module STRICT
  imports DOMAINS
  syntax Val ::= "a"
  syntax Exp ::= Val
               | "b"
               | f(Exp) [strict]
               | g(Exp, Exp) [seqstrict]
               | seqStrict(Exp, Exp) [seqstrict]
               | ndStrict(Exp, Exp) [strict]
  syntax KResult ::= Val

  rule b => a
  rule f(a) => a
  rule g(a,a) => f(b)
  rule seqStrict(a, a) => a
  rule ndStrict(a, a) => a
endmodule
