module MAP-UNIFY-CONCRETE

  imports DOMAINS

  syntax Val ::= "x" | "y" | "z"
               | "success" | "ready"
               | "test1" | "test2" | "test3" | "test4" | "test5"

  configuration
    <T>
      <k> $PGM:Val </k>
      <a> .Map </a>
      <b> .Map </b>
    </T>

  // --- some initial values ---

  // PASS
  rule
    <k> test1 => ready ... </k>
    <a> .Map => x |-> 1 y |-> 2 z |-> 3 </a>
    <b> .Map => x |-> 1 y |-> 2 z |-> 3 </b>

  // PASS
  rule
    <k> test2 => ready ... </k>
    <a> .Map => x |-> 1 y |-> 2 </a>
    <b> .Map => x |-> 1 y |-> 2 z |-> 3 </b>

  // PASS
  rule
    <k> test3 => ready ... </k>
    <a> .Map => x |-> 1 y |-> 2 </a>
    <b> .Map => x |-> 1 z |-> 3 </b>

  // PASS
  rule
    <k> test4 => ready ... </k>
    <b> .Map => x |-> 1 z |-> 3 </b>

  // PASS
  rule
    <k> test5 => ready ... </k>

  // --- compare two maps ---

  rule
    <k> ready => success ... </k>
    <a> M:Map </a>
    <b> M     </b>

endmodule
