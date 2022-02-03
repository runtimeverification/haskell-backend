/*
*/

requires "bmc.k"

module FAIL-1-BMC-SPEC
  imports BMC

  claim (<T> <k> #execute </k> <state> "x" |-> 6 </state> </T>) #Implies (#AG (#Forall X . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies {X <Int 10 #Equals true})))  [kore]

endmodule
