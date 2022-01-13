requires "h.k"

module H4-SPEC
imports H

claim <k> foo(X +Int 1) => . </k>
     <m>
       0 => ?Y -Int 1
     </m>
     ensures X +Int 1 ==Int ?Y -Int 1

endmodule
