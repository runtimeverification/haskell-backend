module EITHER
  imports INT

  syntax Either ::= Left() | Right()
  syntax Bool ::= P( Either , Int ) [function]

  rule P(Left(),I) => true
    requires I >Int 0
  rule P(Right(),I) => true
    requires I >Int 0
  rule P(_E,I) => false
    requires I <=Int 0

endmodule
