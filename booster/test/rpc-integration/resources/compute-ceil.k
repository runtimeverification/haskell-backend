module COMPUTE-CEIL
  imports INT
  imports ID-SYNTAX

  syntax Foo ::= g ( Int )

  rule g ( N:Int ) => N %Int 5

endmodule
