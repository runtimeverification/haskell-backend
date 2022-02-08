requires "test.k"

module TEST-1-SPEC
  imports TEST

  claim a(K:Int |-> V:Int M:Map) => a(3 |-> 2 5 |-> 4)

endmodule
