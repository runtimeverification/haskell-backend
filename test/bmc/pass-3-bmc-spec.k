/*
*/

requires "bmc.k"

module PASS-3-BMC-SPEC
  imports BMC

  claim (<T> <k> #execute </k> <state> "x" |-> 2 </state> </T>) #Implies (#AG(#Forall X . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies {X ==Int 2 #Equals true})))  [kore]

endmodule
