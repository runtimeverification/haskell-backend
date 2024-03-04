module TEST
  imports INT
  imports MAP
  imports STRING

  configuration <k> init ~> getOffset($PGM:ObjectId) </k>
                <objects> <object multiplicity="*" type="Map"> <object-id> obj(0) </object-id> <object-address> 0 </object-address> </object> </objects>
                <memory> .Map </memory>

  syntax KItem ::= "init"
  syntax ObjectId ::= obj(Int)
  syntax Int ::= stackAddress(Int) [function, total, no-evaluators]
  rule <k> init => .K ...</k>
       (.Bag => <object> <object-id> obj(0) </object-id> <object-address> stackAddress(0) </object-address> </object>
                <object> <object-id> obj(1) </object-id> <object-address> stackAddress(1) </object-address> </object>
                <object> <object-id> obj(2) </object-id> <object-address> stackAddress(1) +Int 1 </object-address> </object>)
       <memory> _ => stackAddress(0) |-> 0 stackAddress(1) |-> 1 (stackAddress(1) +Int 1) |-> 2 </memory>

  syntax Int ::= offsetOf(ObjectId) [function]
  rule [offsetOf]: [[ offsetOf(O) => Offset ]]
       <object-id> O </object-id>
       <object-address> A </object-address>
       <memory>... A |-> Offset ...</memory>

  syntax KItem ::= getOffset(ObjectId)
  rule getOffset(O) => offsetOf(O)
endmodule
