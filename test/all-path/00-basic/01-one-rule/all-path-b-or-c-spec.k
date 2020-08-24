module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-B-OR-C-SPEC
  import PATH

  // This should be provable as transiting to b suffices
  // TODO (#1278): ... => ?X ensures ?X ==K b orBool ?X ==K c
  rule <k> a => b #Or c </k> [all-path]

endmodule
