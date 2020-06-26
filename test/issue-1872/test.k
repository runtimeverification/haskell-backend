module TEST
  imports INT

  configuration
    <k> $PGM:Pgm </k>
    <exitcode exit=""> 0 </exitcode>

  syntax Pgm ::= "begin" | "odd"
  rule begin => ?_:Int
  rule I => odd   requires I %Int 2 ==Int 1
endmodule