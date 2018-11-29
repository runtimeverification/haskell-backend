/*
int a, b, sum;
a = 1;
b = 2;
sum = a + b;
*/

module ADDSPEC
  imports IMP

  syntax Id ::= "sum" [token]

  rule
    <k> _ => .K </k>
    <state>... sum |-> (_ => 3) ...</state>

endmodule
