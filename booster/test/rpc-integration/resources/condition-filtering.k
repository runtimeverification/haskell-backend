module CONDITION-FILTERING
  imports INT
  imports BOOL

  syntax State ::= St1() [klabel("S1"), symbol]
                 | St2() [klabel("S2"), symbol]
                 | St3() [klabel("S3"), symbol]

  syntax Bool ::= p ( Int ) [function, total, no-evaluators, klabel("p"), symbol]

  configuration
    <k> $PGM:State </k>
    <x> 0:Int </x>

  rule [s1-to-s2-if-x-0]:
    <k> St1() => St2() </k>
    <x> X </x>
    requires X ==Int 0

  rule [s1-to-s3-if-x-not-0]:
    <k> St1() => St3() </k>
    <x> X </x>
    requires X =/=Int 0

  rule [s2-to-s3-if-p(x)]:
    <k> St2() => St3() </k>
    <x> X </x>
    requires p(X)

  rule [syntactic-equal]:
    X ==Int X => true
    [simplification]

endmodule
