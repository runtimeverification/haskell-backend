module SIMPLIFIED
  imports INT

  syntax Cmd ::=
      "a" Int
    | "b" Int
    | "c" Int
    | "d" Int
    | "aa" Int
    | "bb" Int
    | "cc" Int
    | "dd" Int

  configuration
    <T>
      <k> $PGM:Cmd </k>
      <n> 0:KItem </n>
    </T>

  rule <k> a(X) => f(X) </k>

  rule <k> b(X) => c(X) </k> requires X >Int 0
  rule <k> b(X) => d(X) </k> requires X <=Int 0

  rule <k> c(X) => a(X) </k>
  rule <k> d(X) => a(X) </k>

  rule <k> aa(X) => g(X) </k>

  rule <k> bb(X) => cc(X) </k> requires X >Int 0
  rule <k> bb(X) => dd(X) </k> requires X <=Int 0

  rule <k> cc(X) => aa(X) </k>
  rule <k> dd(X) => aa(X) </k>

  syntax Int ::= t(Int) [function]
  syntax Int ::= s(Int) [function]

  syntax Int ::= f(Int) [function]
  rule f(X) => t(X) requires X >Int 0
  rule f(X) => t(X) requires X <=Int 0

  syntax Int ::= g(Int) [function]

  rule g(X) => s(X) requires X >Int 0 [simplification]
  rule g(X) => s(X) requires X <=Int 0 [simplification]

  rule (t(X) <=Int 0) => (X <=Int 0)  [simplification]
  rule (t(X) >Int 0) => (X >Int 0)    [simplification]
  rule (s(X) <=Int 0) => (X <=Int 0)  [simplification]
  rule (s(X) >Int 0) => (X >Int 0)    [simplification]
  rule (f(X) <=Int 0) => (X <=Int 0)  [simplification]
  rule (f(X) >Int 0) => (X >Int 0)    [simplification]
  rule (g(X) <=Int 0) => (X <=Int 0)  [simplification]
  rule (g(X) >Int 0) => (X >Int 0)    [simplification]

endmodule
