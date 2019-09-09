/*
*/

module VERIFICATION
  imports BMC

endmodule


module TEST4-SPEC
  imports VERIFICATION
  imports BMC

  rule (<T> <k> #execute </k> <state> "x" |-> X </state> </T> #And {(5 <Int X andBool X <Int 8) #Equals true}) #Implies (#AG(#Forall X . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies {X <Int 8 #Equals true})))  [kore]

endmodule
