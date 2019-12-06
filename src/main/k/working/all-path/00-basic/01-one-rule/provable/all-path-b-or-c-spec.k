module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-B-OR-C-SPEC
  import PATH
  
  // This should be provable as transiting to b suffices
  rule <k> a => ?X </k>
    ensures ?X ==K b orBool ?X ==K c [all-path]

endmodule
