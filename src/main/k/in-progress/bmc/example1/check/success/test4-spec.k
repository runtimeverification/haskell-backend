/*
*/

module VERIFICATION
  imports BMC

endmodule


module TEST4-SPEC
  imports VERIFICATION
  imports BMC

  rule (<T> <k> #execute </k> <state> "x" |-> 6 </state> </T>) #Implies (#AG(#Forall X . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies {X >=Int 6 #Equals true})))  [kore]

endmodule
