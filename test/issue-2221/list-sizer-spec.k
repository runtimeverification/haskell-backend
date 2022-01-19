requires "list-sizer.k"

module VERIFICATION
  imports LIST-SIZER

endmodule

module LIST-SIZER-SPEC
  imports VERIFICATION

  claim <k> _:MyList => .K </k>
        <size> 0 </size>

endmodule

