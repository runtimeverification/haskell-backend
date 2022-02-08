requires "with-config.k"

module ONE-SPEC
    imports WITH-CONFIG

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
