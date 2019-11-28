module VERIFICATION
  imports UNIFICATION
endmodule


module FUNCTION-UNIFICATION-SPEC
  imports VERIFICATION
  imports UNIFICATION

  rule
    ! (notBool X:Bool) => X
endmodule
