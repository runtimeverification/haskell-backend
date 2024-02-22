module TEST
  imports INT
  imports BOOL

  syntax State ::= "init" [token]
                 | "a"    [token]
                 | "b"    [token]
                 | "c"    [token]
                 | "d"    [token]

                 | "jnit" [token]
                 | "e"    [token]
                 | "f"    [token]
                 | "g"    [token]

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
 //-----------------------------

  rule [JNIT-E]: <k> jnit => e ... </k>
                 <int> X        </int>
                 requires X ==Int 42 andBool X =/=Int 42
  rule [JNIT-F]: <k> jnit => f ... </k>
  rule [EG]: <k> e => g ... </k>
  rule [FG]: <k> f => g ... </k>

endmodule
