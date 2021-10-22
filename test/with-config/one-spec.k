requires "with-config.k"

module VERIFICATION
    imports WITH-CONFIG

    syntax KItem ::= "A" "(" AccountId ")"
    rule A(AID) => total_balance(AID)
endmodule

module ONE-SPEC
    imports VERIFICATION

    claim <k> A(AID) => 30 </k>
        <accounts>
            <account>
                <accountID> AID </accountID>
                <freeBalance> 30 </freeBalance>
            </account>
        </accounts>
endmodule