// Copyright (c) 2019 K Team. All Rights Reserved.

module TEST-SYNTAX
    imports INT
    imports K-EQUAL

    syntax Pgm ::= Instr
    syntax Instr ::= "MIN" Int Int

endmodule

module TEST
    imports TEST-SYNTAX

    configuration
      <k> $PGM:Pgm </k>
      <a> 0 </a>

    rule <k> MIN X Y => .K ... </k>
         <a> _ => X </a>
      requires X <=Int Y

    rule <k> MIN X Y => .K ... </k>
         <a> _ => Y </a>
      requires Y <Int X

endmodule
