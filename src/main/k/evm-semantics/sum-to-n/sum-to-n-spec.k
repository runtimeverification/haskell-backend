requires "asm.k"
requires "edsl.k"

module VERIFICATION
    imports EDSL
    imports EVM-ASSEMBLY

    rule #sizeWordStack ( WS , N:Int )
      => N +Int #sizeWordStack ( WS , 0 )
      requires N =/=K 0
      [lemma]

    syntax ByteArray ::= "sumToN" [function]
 // ----------------------------------------
    rule sumToN
      => #asmOpCodes(PUSH(1, 0) ; SWAP(1)                   // s = 0 ; n = N
                    ; JUMPDEST                              // label:loop
                    ; DUP(1) ; ISZERO ; PUSH(1, 20) ; JUMPI // if n == 0, jump to end
                    ; DUP(1) ; SWAP(2) ; ADD                // s = s + n
                    ; SWAP(1) ; PUSH(1, 1) ; SWAP(1) ; SUB  // n = n - 1
                    ; PUSH(1, 3) ; JUMP                     // jump to loop
                    ; JUMPDEST                              // label:end
                    ; .OpCodes
                    ) [macro]
endmodule

module SUM-TO-N-SPEC
    imports VERIFICATION

    rule <k> #execute ... </k>
         <mode> NORMAL </mode>
         <schedule> DEFAULT </schedule>
         <callStack> .List </callStack>
         <memoryUsed> 0   </memoryUsed>
         <localMem> .Map </localMem>
         <callGas> _ => _ </callGas>
         <program> sumToN </program>
         <jumpDests> JUMPDESTS </jumpDests>

         <pc>        0  => 21                                </pc>
         <wordStack> N : WS => 0 : N *Int (N +Int 1) /Int 2 : WS </wordStack>
         <gas>       G  => G -Int (52 *Int N +Int 27)        </gas>
         <static> STATIC </static>

      requires N >=Int 0
       andBool N <=Int 340282366920938463463374607431768211455
       andBool 0 <=Int #sizeWordStack(WS)
       andBool #sizeWordStack(WS) <Int 1021
       andBool G >=Int 52 *Int N +Int 27
       andBool JUMPDESTS ==K #computeValidJumpDests(sumToN)

endmodule
