requires "with-config.k"

module VERIFICATION
    imports WITH-CONFIG

    syntax KItem ::= "a" "(" AccountId ")"
    rule a(AID) => total_balance(AID)
endmodule

module OWISE-SPEC
    imports VERIFICATION

    claim <k> a(AID) => 0 </k>
        <accounts>
            <account>
                <accountID> BID </accountID>
                <freeBalance> 30 </freeBalance>
            </account>
        </accounts>
        requires AID =/=K BID
endmodule
