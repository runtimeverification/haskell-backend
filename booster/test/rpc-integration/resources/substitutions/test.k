module TEST
  import INT

  syntax State ::= "symbolic-subst" [token]
                 | "concrete-subst" [token]
                 | "a"              [token]

  configuration <k> $PGM:State ~> .K </k>
                <int> 0:Int </int>
                <jnt> 0:Int </jnt>

  rule [symbolic-subst]:
               <k> symbolic-subst => a ... </k>
               <int> X        </int>
               <jnt> Y        </jnt>
               ensures X ==Int Y
  //----------------------------
  rule [concrete-subst]:
               <k> concrete-subst => a ... </k>
               <int> X                     </int>
               ensures X ==Int 42

endmodule
