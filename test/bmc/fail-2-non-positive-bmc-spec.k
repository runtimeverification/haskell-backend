/*
*/

requires "bmc.k"

module FAIL-2-NON-POSITIVE-BMC-SPEC
  imports BMC

  claim (<T> <k> #execute </k> <state> "x" |-> X </state> </T> #And {X >Int 0 #Equals false}) #Implies (#AG(#Forall Y . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> Y </state> </T>) #Implies {X ==Int Y #Equals true})))  [kore]

endmodule
