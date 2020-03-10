module KREFLECTION
  imports K-REFLECTION-SYMBOLIC
  imports K-REFLECTION

  syntax Concrete ::= "concrete"

  rule concrete => #isConcrete(?_)

endmodule
