module ORD
  imports STRING
    syntax String ::= rlpEncodeString ( String )           [function]
    syntax String ::= rlpEncodeLength ( String , Int )     [function]

    rule rlpEncodeString(STR) => STR                       requires lengthString(STR) ==Int 1 andBool ordChar(STR) <Int 128
    rule rlpEncodeString(_)   => "Error"                   [owise]


    configuration <k> rlpEncodeString($PGM:String) </k>
    rule <k> "Error" => .K </k>
endmodule

