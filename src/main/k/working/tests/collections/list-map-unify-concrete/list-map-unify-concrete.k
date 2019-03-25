module LIST-MAP-UNIFY-CONCRETE

    imports DOMAINS

    configuration <k> $PGM:Program </k>
                  <acct> 0 </acct>
                  <accounts>
                    <account multiplicity="*" type="Map">
                      <acctID>      0    </acctID>
                      <storage>     .Map </storage>
                      <origStorage> .Map </origStorage>
                    </account>
                  </accounts>

    syntax KItem ::= Int
 // --------------------

    syntax Program ::= ".Program"
                     | Command ";" Program
 // --------------------------------------
    rule <k> C ; P => C ~> P ... </k>

    syntax Command ::= newAccount ( Int )
 // -------------------------------------
    rule <k> newAccount(ACCT) => . ... </k>
         <accounts>
           ( .Bag
          => <account>
               <acctID> ACCT </acctID>
               ...
             </account>
           )
           ...
         </accounts>

    syntax Command ::= setAccount ( Int )
 // -------------------------------------
    rule <k> setAccount(ACCT) => . ... </k>
         <acct> _ => ACCT </acct>

    syntax Command ::= write ( Int , Int )
 // --------------------------------------
    rule <k> write(KEY, VALUE) => . ... </k>
         <acct> ACCT </acct>
         <account>
            <acctID> ACCT </acctID>
            <storage> STORAGE => STORAGE [ KEY <- VALUE ] </storage>
            ...
         </account>

    syntax Command ::= finalize ( List )
 // ------------------------------------
    rule <k> finalize(.List) => . ... </k>

    rule <k> finalize((ListItem(ACCT) => .List) _) ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           <origStorage> _ => STORAGE </origStorage>
           ...
         </account>
endmodule
