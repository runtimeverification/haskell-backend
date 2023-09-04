module TEST
  import INT
  import BOOL

  syntax State ::= "init" [token]
                 | "a"    [token]
                 | "b"    [token]
                 | "c"    [token]
                 | "d"    [token]

  configuration <k> $PGM:State ~> .K </k>
                <int> 0:Int          </int>

  rule [init]: <k> init => a ... </k>
               <int> X        </int>
               ensures X ==Int 42

  rule [AB]: <k> a => b ... </k>
  rule [AC]: <k> a => c ... </k>
             <int> X        </int>
             ensures X =/=Int 42
  rule [BD]: <k> b => d ... </k>
  rule [CD]: <k> c => d ... </k>

endmodule
