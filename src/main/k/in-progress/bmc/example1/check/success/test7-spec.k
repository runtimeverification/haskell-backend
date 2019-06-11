/*
*/

module VERIFICATION
  imports BMC

endmodule


module TEST7-SPEC
  imports VERIFICATION
  imports BMC

  rule (<T> <k> #execute </k> <state> "x" |-> X </state> </T> #And {(0 <Int X andBool X <Int 4) #Equals true}) #Implies (#AG(#Forall Y . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> Y </state> </T>) #Implies {X ==Int Y #Equals true})))  [kore]

endmodule
