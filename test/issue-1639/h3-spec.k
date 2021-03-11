module H3-SPEC
imports H

claim <k> foo(X) => . </k>
     <m>
      0 => ?Y -Int 1
     </m>
     ensures X ==Int ?Y -Int 1

endmodule