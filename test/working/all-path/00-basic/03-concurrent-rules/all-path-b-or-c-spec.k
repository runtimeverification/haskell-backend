module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-B-OR-C-SPEC
  imports VERIFICATION
  imports PATH

// This should be provable as both one-path and all-path.
  rule <k> a => ?X </k> 
    ensures ?X ==K b orBool ?X ==K c [all-path]

endmodule
