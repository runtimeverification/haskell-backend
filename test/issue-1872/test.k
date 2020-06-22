module TEST
  imports INT

  configuration
    <k> $PGM:Pgm </k>
    <exitcode exit=""> 0 </exitcode>

  syntax Pgm ::= "begin" | "even" | "odd"
  rule begin => ?_:Int
  rule I => even  requires I %Int 2 ==Int 0
  rule I => odd   requires I %Int 2 ==Int 1
endmodule