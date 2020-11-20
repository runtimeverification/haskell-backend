module VERIFICATION
    imports WITH-CONFIG

    syntax EntryAction ::= totalBalance ( AccountId )
    rule <k> totalBalance(AID) => total_balance(AID) ... </k>
endmodule

module ONE-SPEC
    imports VERIFICATION

    claim <k> totalBalance(AID) => 50 ... </k>
        <accounts>
            <account>
                <accountID> AID </accountID>
                <freeBalance> 30 </freeBalance>
                <reservedBalance> 20 </reservedBalance>
                ...
            </account>
            ...
        </accounts>
endmodule