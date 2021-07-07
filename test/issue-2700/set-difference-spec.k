module VERIFICATION
    imports SET-DIFFERENCE
endmodule

module SET-DIFFERENCE-SPEC
    imports VERIFICATION

    claim [claim.diff.empty]:
          <k> run(.Set -Set SetItem(_X)) => done(.Set) ... </k>

    claim [claim.concat]:
          <k> run((SetItem(X) REST) -Set SetItem(Y)) =>
              done(SetItem(X) (REST -Set SetItem(Y))) ... </k>
      requires notBool pred(X) andBool pred(Y)

    claim [claim.diff.both.concrete.singletons]:
          <k> run(SetItem(1) -Set SetItem(10)) => done(SetItem(1)) ... </k>

    claim [claim.diff.left.concrete.singleton]:
          <k> run(SetItem(1) -Set SetItem(X)) => done(SetItem(1)) ... </k>
      requires pred(X)

    // This claim does not pass, am I missing something?
    // claim [claim.diff.left.symbolic.singleton]:
    //       <k> run(SetItem(X) -Set SetItem(10)) => done(SetItem(X)) ... </k>
    //   requires notBool pred(X)

    claim [claim.diff.symbolic.singletons]:
          <k> run(SetItem(X) -Set SetItem(Y)) => done(SetItem(X)) ... </k>
      requires notBool pred(X) andBool pred(Y)
endmodule