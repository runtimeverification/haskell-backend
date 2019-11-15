module PATH
  import DOMAINS
  syntax S ::= "a" | "b" | "c"
  syntax T ::= f(S) | g(S) | "end"

  rule f(a) => end
  rule f(b) => end
  rule f(c) => end

  rule g(a) => end
  rule g(b) => end
endmodule
