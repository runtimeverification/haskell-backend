module SET-UNIFY-CONCRETE

  imports DOMAINS

  syntax Val ::= "x" | "y" | "z"
               | "success" | "ready"
               | "test1" | "test2" | "test3" | "test4" | "test5"

  configuration
    <T>
      <k> $PGM:Val </k>
      <a> .Set </a>
      <b> .Set </b>
    </T>

  // --- some initial values ---

  // PASS
  rule
    <k> test1 => ready ... </k>
    <a> .Set => SetItem(x) SetItem(y) SetItem(z) </a>
    <b> .Set => SetItem(x) SetItem(y) SetItem(z) </b>

  // PASS
  rule
    <k> test2 => ready ... </k>
    <a> .Set => SetItem(x) SetItem(y) </a>
    <b> .Set => SetItem(x) SetItem(y) SetItem(z) </b>

  // PASS
  rule
    <k> test3 => ready ... </k>
    <a> .Set => SetItem(x) SetItem(y) </a>
    <b> .Set => SetItem(x) SetItem(z) </b>

  // PASS
  rule
    <k> test4 => ready ... </k>
    <b> .Set => SetItem(x) SetItem(z) </b>

  // PASS
  rule
    <k> test5 => ready ... </k>

  // --- compare two sets ---

  rule
    <k> ready => success ... </k>
    <a> L1:Set </a>
    <b> L1      </b>

endmodule
