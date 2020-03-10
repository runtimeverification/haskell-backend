module ITETEST
  imports K-EQUAL
  imports INT
  syntax S ::= "test" | Int
  configuration <k> $PGM:K </k>

  rule test => #if true #then 0 #else 1 #fi
endmodule
