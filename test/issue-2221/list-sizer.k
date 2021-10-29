module LIST-SIZER-SYNTAX
  imports INT-SYNTAX

  syntax MyList ::= ".MyList"
                  | Int MyList

endmodule

module LIST-SIZER
  imports LIST-SIZER-SYNTAX
  imports INT
  imports LIST

  configuration <k> $PGM:MyList </k>
                <size> 0 </size>

  rule <k> .MyList => .K </k>

  rule <k> _E L:MyList => L </k>
       <size> N => N +Int 1 </size>

endmodule
