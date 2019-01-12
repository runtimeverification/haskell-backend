module SET-UNIFY-CONCRETE-2

  imports DOMAINS

  syntax Val ::= "x" | "y" | "z" | "t"
               | "success" | "ready"
               | "test1" | "test2" | "test3"

  configuration
    <T>
      <k> $PGM:Val </k>
      <a> SetItem(x) SetItem(y) SetItem(z) </a>
      <b> ready </b>
    </T>

  // PASS
  rule
    <k> test1 </k>
    <a> SetItem(x) SetItem(y) SetItem(z) </a>
    <b> ready => success </b>

  // CRASH (z3 issue?)
  rule
    <k> test2 </k>
    <a> SetItem(x) SetItem(y) </a>
    <b> ready => success </b>

  // CRASH (z3 issue?)
  rule
    <k> test3 </k>
    <a> SetItem(x) SetItem(y) SetItem(z) SetItem(t) </a>
    <b> ready => success </b>

endmodule
