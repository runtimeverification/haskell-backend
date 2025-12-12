module TEST
  imports BOOL
  imports INT

  // sorts involved
  syntax Evaluation ::= Value | Stuff
  syntax Value ::= Integer ( Int ) [symbol(Integer)]
  syntax Stuff ::= Stuff()         [symbol(Stuff)]
  syntax Wrap ::= Wrap ( Int )     [symbol(Wrap)]

  // lookup function, two-stage
  // upper level, dispatching
  syntax Evaluation ::= lookup ( Wrap ) [function, total, symbol(lookup), no-evaluators]
  //        The no-evaluators here leads to the HS backend evaluating it  ^^^^^^^^^^^^^
  rule [dispatch]: lookup(Wrap(N)) => lookup0(N) requires N %Int 1 ==Int 0

  syntax Evaluation ::= lookup0 ( Int ) [function, total, symbol(lookup0)]
  // ----------------------------------------------------
  rule [notfound]: lookup0(_N) => Stuff() [owise]
  rule [target]:   lookup0(42) => Integer(42)

  // test harness
  syntax KItem ::= Run ( Int )    [symbol(Run)]
                 | Done ( Value ) [symbol(Done)]
                 | Fail ( Int )   [symbol(Fail)]

  rule [run-done]: Run(I) => Done(Integer(I)) requires isValue( lookup(Wrap(I)) )
  rule [run-fail]: Run(I) => Fail(I) [owise]

endmodule
