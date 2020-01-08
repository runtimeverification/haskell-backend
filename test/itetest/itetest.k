module ITETEST
  imports K-EQUAL
  imports DOMAINS
  syntax S ::= "test" | Int
  configuration <k> $PGM:K </k>

  rule test => #if true #then 0 #else 1 #fi
endmodule
