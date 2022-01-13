requires "test.k"

module VERIFICATION
  imports TEST
  imports BOOL

endmodule

module TEST-SPEC
  imports VERIFICATION

  claim <k> makeLookup(B) => 1 ... </k>
    requires lookup(#hashedLocation(B .IntList)) ==Int 1
     andBool #rangeUInt(B)
endmodule
