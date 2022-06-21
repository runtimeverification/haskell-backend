module TEST-SPEC
    imports TEST

    claim [reaches-zero]:
        <k> foo(N) => foo(0) </k>
      requires N >=Int 0
endmodule
