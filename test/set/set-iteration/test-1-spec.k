requires "test.k"

module TEST-1-SPEC
  imports TEST

  claim <k> runTest( f( SetItem(a) SetItem(b) ) ) </k>
    => <k> doneTest( SetItem(b) SetItem(c) ) </k>

endmodule
