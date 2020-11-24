module H2-SPEC
imports H

claim <k> foo(X +Int 1) => . </k>
     <m>
       0 => ?Y
     </m>
     ensures X +Int 1 ==Int ?Y

endmodule