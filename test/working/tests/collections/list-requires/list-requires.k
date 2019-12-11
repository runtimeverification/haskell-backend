module LIST-REQUIRES

  imports DOMAINS
  imports COLLECTIONS

  syntax Val ::= "a" | "b"

  configuration
    <T>
      <k> $PGM:Val </k>
      <sl> (b |-> 0) (a |-> b) </sl>
      <sr> (a |-> b) </sr>
    </T>

syntax Map ::= removeAs ( Map ) [function, functional]
             | removeAs ( List , Map ) [function, functional]
// ------------------------------------------------------------------------------
rule removeAs( M )                                   => removeAs(Set2List(keys(M)), M)
//rule removeAs( .List, .Map )                         => .Map
//rule removeAs( ListItem(KEY) L, KEY |-> 0 REST )     => removeAs(L, REST)
//rule removeAs( ListItem(KEY) L, KEY |-> VALUE REST ) => KEY |-> VALUE removeAs(L, REST) requires VALUE =/=K 0
rule removeAs(.List, M) => M
rule removeAs(ListItem(KEY) L, M) => #if M[KEY] ==K 0 #then removeAs(L, M[KEY <- undef]) #else removeAs(L, M) #fi
//    requires KEY in_keys(M)

rule
    <k> a => b </k>
    <sl> ACCTSTORAGE </sl>
    <sr> STORAGE </sr>
    requires removeAs(ACCTSTORAGE) ==K STORAGE


endmodule
