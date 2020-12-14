module VERIFICATION
    imports WITH-CONFIG

    syntax KItem ::= "A" "(" AccountId ")"
    rule A(AID) => total_balance(AID)
endmodule

module OWISE-SPEC
    imports VERIFICATION

    claim <k> A(AID) => 0 </k>
        <accounts>
            <account>
                <accountID> BID </accountID>
                <freeBalance> 30 </freeBalance>
            </account>
        </accounts>
        requires AID =/=K BID
endmodule