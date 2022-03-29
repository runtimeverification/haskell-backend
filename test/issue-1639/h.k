// Description of the issue in https://github.com/runtimeverification/haskell-backend/issues/1639
module H

imports BOOL
imports INT
imports MAP

configuration <T> <k> $PGM:Cmd </k> <m> 0 </m> </T>

syntax Cmd ::= foo(Int)
rule <k> foo(X) => . ... </k>
     <m>
       0 => X
     </m>

endmodule
