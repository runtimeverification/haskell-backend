
module VERIFICATION
  imports SETVARS

endmodule


module DIV-SPEC
  imports VERIFICATION
  imports SETVARS

  rule
    <k>
        j(X:Int, j(X,X)) => X
    </k>
  requires  X =/=Int 0

endmodule
