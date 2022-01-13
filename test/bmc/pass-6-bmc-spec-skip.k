/*
*/

requires "bmc.k"

module VERIFICATION
  imports BMC

endmodule


module PASS-6-BMC-SPEC
  imports VERIFICATION
  imports BMC

  rule (<T> <k> #execute </k> <state> "x" |-> X </state> </T> #And {X <Int -2 #Equals true}) #Implies (#AG(#Forall Y . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> Y </state> </T>) #Implies {Y <=Int 0 #Equals true})))  [kore]

endmodule
