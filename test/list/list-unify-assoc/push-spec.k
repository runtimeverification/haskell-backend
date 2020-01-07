module VERIFICATION

  imports TEST

endmodule

module PUSH-SPEC

  imports VERIFICATION

  rule
    <k> push(X) => . ... </k>
    <stack> _ => _ </stack>

endmodule
