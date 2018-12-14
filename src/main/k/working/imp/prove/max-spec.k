/*
*/

module MAX-SPEC
  imports IMP

  syntax Id ::= "a" [token]
  syntax Id ::= "b" [token]
  syntax Id ::= "max" [token]

  rule
    <k>
if (a <= b)
{ max = b; }
else
{ max = a; }
=> .K
    </k>
    <state>
    a |-> A:Int
    b |-> B:Int
    max |-> (_ => A)
    </state>
    requires A >Int B

endmodule
