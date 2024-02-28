// Copyright (c) 2020 K Team. All Rights Reserved.

module TEST-SYNTAX
    imports INT

    syntax Pgm ::= loop ( Int )
endmodule

module TEST
    imports TEST-SYNTAX

    configuration
      <k> $PGM:Pgm </k>
      <counter> 1 </counter>
      <sum> 0 </sum>

    rule
      <k> loop(0) => .K ... </k>
    rule
      <k> loop(Times:Int => Times -Int 1) ...</k>
      <counter> C:Int => C +Int 1 </counter>
      <sum> S:Int => S +Int C </sum>
      requires Times >Int 0
endmodule
