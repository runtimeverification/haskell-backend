/*
*/

requires "bmc.k"

module VERIFICATION
  imports BMC

endmodule


module PASS-2-BMC-SPEC
  imports VERIFICATION
  imports BMC

  claim (<T> <k> #execute </k> <state> "x" |-> 0 </state> </T>) #Implies (#AG(#Forall X . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies {X ==Int 0 #Equals true})))  [kore]

endmodule
