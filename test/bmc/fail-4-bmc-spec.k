/*
*/

module VERIFICATION
  imports BMC

endmodule


module FAIL-4-BMC-SPEC
  imports VERIFICATION
  imports BMC

  claim (<T> <k> #execute </k> <state> "x" |-> X </state> </T> #And {(5 <Int X andBool X <Int 8) #Equals true}) #Implies (#AG(#Forall X . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies {X <Int 8 #Equals true})))  [kore]

endmodule
