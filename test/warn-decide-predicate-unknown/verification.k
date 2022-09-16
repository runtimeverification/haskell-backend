requires "./lemmas.k"

module VERIFICATION
    imports LEMMAS

    syntax StepSort ::= Int | Bool
 // ------------------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule <k> runLemma( T ) => doneLemma( T ) ... </k>

endmodule