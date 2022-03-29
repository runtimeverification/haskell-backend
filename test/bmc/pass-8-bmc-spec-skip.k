/*
*/

requires "bmc.k"

module PASS-8-BMC-SPEC
  imports BMC

  rule (<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies (#AG(#Forall Y . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> Y </state> </T>) #Implies {X <=Int Y #Equals true})))  [kore]

endmodule
