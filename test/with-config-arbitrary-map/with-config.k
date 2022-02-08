module WITH-CONFIG
    imports INT
    imports MAP
    imports COLLECTIONS

    configuration
        <set-balance>
            <k> $ACTION:Action </k>
            <accounts>
                <account multiplicity="*" type="Map">
                    <accountID> .AccountId:AccountId </accountID>
                    <freeBalance> 0 </freeBalance>
                    <reservedBalance> 0 </reservedBalance>
                </account>
            </accounts>
        </set-balance>

    syntax Action ::= ".Action" | EntryAction
    syntax EntryAction ::= ".EntryAction"

    syntax AccountId ::= ".AccountId" | Int
    // ---------------------------------------

    syntax Int ::= "total_balance" "(" AccountId ")" [function, functional]
    // -----------------------------------------------------------------------
    rule total_balance(WHO) => free_balance(WHO) +Int reserved_balance(WHO)

    syntax Int ::= "free_balance" "(" AccountId ")" [function, functional]
    // ----------------------------------------------------------------------
    rule    free_balance(_)   => 0 [owise]
    rule [[ free_balance(WHO) => FREE_BALANCE ]]
        <account>
            <accountID> WHO </accountID>
            <freeBalance> FREE_BALANCE </freeBalance>
            ...
        </account>

    syntax Int ::= "reserved_balance" "(" AccountId ")" [function, functional]
    // --------------------------------------------------------------------------
    rule    reserved_balance(_)   => 0 [owise]
    rule [[ reserved_balance(WHO) => FREE_BALANCE ]]
        <account>
            <accountID> WHO </accountID>
            <reservedBalance> FREE_BALANCE </reservedBalance>
            ...
        </account>

    // for one-spec
    syntax EntryAction ::= totalBalance ( AccountId )
    rule <k> totalBalance(AID) => total_balance(AID) ... </k>

endmodule