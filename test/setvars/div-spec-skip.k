requires "setvars.k"

module DIV-SPEC
  imports SETVARS

  rule
    <k>
        j(X:Int, j(X,X)) => X
    </k>
  requires  X =/=Int 0

endmodule
