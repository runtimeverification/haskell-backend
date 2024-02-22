module PATH
  imports BOOL
  syntax S ::= "a" | "b" | "c"
  syntax T ::= total(S) | partial(S) | "end"

  rule total(a) => end
  rule total(b) => end
  rule total(c) => end

  rule partial(a) => end
  rule partial(b) => end
endmodule
