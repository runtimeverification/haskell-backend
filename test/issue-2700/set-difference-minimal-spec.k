module VERIFICATION
    imports SET-DIFFERENCE-MINIMAL
endmodule

module SET-DIFFERENCE-MINIMAL-SPEC
    imports VERIFICATION

    claim [claim.diff.left.symbolic.singleton]:
          <k> run(SetItem(X) -Set SetItem(10)) => done(SetItem(X)) ... </k>
          requires X =/=Int 10

endmodule