module NON-LINEAR-INT-REQUIRES
  imports INT
  imports BOOL

  syntax State ::= "init"   [token]
                 | "target" [token]

  configuration <k> $PGM:State ~> .K </k>
                <x-int> 0:Int          </x-int>
                <y-int> 0:Int          </y-int>

  rule [transition]: <k> init => target ... </k>
                     <x-int> X              </x-int>
                     <y-int> Y              </y-int>
       requires X <Int (X *Int Y +Int Y) /Int (Y /Int X)

endmodule
