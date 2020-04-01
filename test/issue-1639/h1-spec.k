module H1-SPEC
imports H

rule <k> foo(X) => . </k>
     <m>
       0 => ?Y
     </m>
     ensures X ==Int ?Y

endmodule