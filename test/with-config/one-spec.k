requires "with-config.k"

module ONE-SPEC
    imports WITH-CONFIG

    claim <k> aa(AID) => 30 </k>
        <accounts>
            <account>
                <accountID> AID </accountID>
                <freeBalance> 30 </freeBalance>
            </account>
        </accounts>
endmodule