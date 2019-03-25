
module VERIFICATION
  imports IMP
//
// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]


  syntax Stmt ::= "loop"    [function]
  syntax Pgm  ::=  main(Int) [function]


  rule loop => 
       while (!(n <= 0)) {
        sum = sum + n + n;
        n = n + -1;
      }

  rule main(N:Int) =>
      int n, sum;
      n = N:Int;
      sum = 0;
      while (!(n <= 0)) {
        sum = sum + n + n;
        n = n + -1;
      }
 
endmodule
