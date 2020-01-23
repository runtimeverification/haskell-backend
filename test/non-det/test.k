module TEST
  syntax KItem ::= "Det"
  // Det rewrites deterministically to true
  rule Det => true

  syntax KItem ::= "NonDet"
  // NotDet rewrites non-deterministically to true and false
  rule NonDet => true
  rule NonDet => false
endmodule
