requires "with-config.k"

module VERIFICATION
    imports WITH-CONFIG

    syntax KItem ::= "aa" "(" AccountId ")"
    rule aa(AID) => total_balance(AID)
endmodule

module ONE-SPEC
    imports VERIFICATION

    claim <k> aa(AID) => 30 </k>
        <accounts>
            <account>
                <accountID> AID </accountID>
                <freeBalance> 30 </freeBalance>
            </account>
        </accounts>
endmodule