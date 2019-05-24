module VERIFICATION
  imports HARNESS
endmodule

module MAP-SPEC

  imports VERIFICATION
  imports COLLECTIONS

  // _Map_: identity
  rule <k> eval (a |-> b .Map) => eval (a |-> b) </k>
  rule <k> eval (.Map a |-> b) => eval (a |-> b) </k>

  // _Map_: idempotent
  rule <k> eval (a |-> b a |-> b) => eval (a |-> b) </k>

  // [Error] Critical: failed to concatenate maps with common keys
  // rule <k> eval (a |-> b a |-> c) => eval (a |-> c) </k>

endmodule
