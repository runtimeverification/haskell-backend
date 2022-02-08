/*
*/

requires "bmc.k"

module PASS-1-BMC-SPEC
  imports BMC

  claim (<T> <k> #execute </k> <state> "x" |-> -3 </state> </T>) #Implies (#AG(#Forall X . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies {X <=Int 0 #Equals true})))  [kore]

endmodule
