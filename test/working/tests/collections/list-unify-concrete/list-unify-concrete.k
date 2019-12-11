module LIST-UNIFY-CONCRETE

  imports DOMAINS

  syntax Val ::= "x" | "y" | "z"
               | "success" | "ready"
               | "test1" | "test2" | "test3" | "test4" | "test5"

  configuration
    <T>
      <k> $PGM:Val </k>
      <a> .List </a>
      <b> .List </b>
    </T>

  // --- some initial values ---

  // PASS
  rule
    <k> test1 => ready ... </k>
    <a> .List => ListItem(x) ListItem(y) ListItem(z) </a>
    <b> .List => ListItem(x) ListItem(y) ListItem(z) </b>

  // PASS
  rule
    <k> test2 => ready ... </k>
    <a> .List => ListItem(x) ListItem(y) </a>
    <b> .List => ListItem(x) ListItem(y) ListItem(z) </b>

  // PASS
  rule
    <k> test3 => ready ... </k>
    <a> .List => ListItem(x) ListItem(y) </a>
    <b> .List => ListItem(x) ListItem(z) </b>

  // PASS
  rule
    <k> test4 => ready ... </k>
    <b> .List => ListItem(x) ListItem(z) </b>

  // PASS
  rule
    <k> test5 => ready ... </k>

  // --- compare two lists ---

  rule
    <k> ready => success ... </k>
    <a> L1:List </a>
    <b> L1      </b>

endmodule
