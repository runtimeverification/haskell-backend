module VERIFICATION
  imports HARNESS
endmodule

module SET-SPEC

  imports VERIFICATION
  imports COLLECTIONS

  // _Set_: identity
  rule <k> eval (SetItem(a) .Set) => eval SetItem(a) </k>
  rule <k> eval (.Set SetItem(a)) => eval SetItem(a) </k>

  // _Set_: idempotent
  rule <k> eval (SetItem(a) SetItem(a)) => eval SetItem(a) </k>

  // _Set_: preserves keys
  rule <k> eval (SetItem(a) SetItem(b)) => eval (SetItem(a) SetItem(b)) </k>

endmodule