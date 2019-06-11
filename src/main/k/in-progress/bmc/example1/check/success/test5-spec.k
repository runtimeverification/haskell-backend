/*
*/

module VERIFICATION
  imports BMC

endmodule


module TEST5-SPEC
  imports VERIFICATION
  imports BMC

  rule (<T> <k> #execute </k> <state> "x" |-> X </state> </T> #And {(0 <Int X andBool X <Int 4) #Equals true}) #Implies (#AG(#Forall X . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies {X <Int 4 #Equals true})))  [kore]

endmodule
