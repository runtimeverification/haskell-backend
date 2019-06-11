/*
*/

module VERIFICATION
  imports BMC

endmodule


module TEST3-SPEC
  imports VERIFICATION
  imports BMC

  rule (<T> <k> #execute </k> <state> "x" |-> X </state> </T> #And {0 <Int X #Equals true}) #Implies (#AG(#Forall Y . #Forall _ .((<T> <k> _ </k> <state> "x" |-> Y </state> </T>) #Implies {0 <Int Y #Equals true})))  [kore]

endmodule
