requires "test.k"

module TEST-SPEC
  imports TEST
  imports BOOL

  claim <k> makeLookup(B) => 1 ... </k>
    requires lookup(#hashedLocation(B .IntList)) ==Int 1
     andBool #rangeUInt(B)
endmodule
