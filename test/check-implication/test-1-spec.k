module VERIFICATION
  imports TEST
endmodule

module TEST-1-SPEC
  imports VERIFICATION

  claim a(K:Int |-> V:Int M:Map) => a(3 |-> 2 5 |-> 4)

endmodule
