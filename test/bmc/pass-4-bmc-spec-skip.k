/*
*/

requires "bmc.k"

module PASS-4-BMC-SPEC
  imports BMC

  rule (<T> <k> #execute </k> <state> "x" |-> 6 </state> </T>) #Implies (#AG(#Forall X . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies {X >=Int 6 #Equals true})))  [kore]

endmodule
