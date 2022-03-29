module PRIORITY
  imports INT
  imports BOOL
  imports K-EQUAL

  syntax S ::= "one" | "two" | "three" | "four" | "five" | "six" | "seven" | start(Int) | middle(Int)
  rule one => two [priority(1)]
  rule one => three [priority(2)]

  rule start(X) => one       requires X <Int 0  [priority(1)]
  rule start(X) => one       requires X >=Int 0 andBool X <Int 5  [priority(1)]
  rule start(X) => middle(X) requires X <Int 10 [priority(2), label(first)]
  rule start(X) => one                          [priority(3)]

  rule middle(X) => one requires X <Int 6 [priority(1)]
  rule middle(X) => two requires X >Int 8 [priority(2), label(second)]
  rule middle(X) => one                   [priority(3), label(third)]

  syntax S ::= func1(Int)     [function]
  rule func1(X:Int) => four
    requires X ==Int 4
  rule func1(4)     => four
  rule func1(_:Int) => seven  [priority(49)]

  syntax S ::= func2(Int)     [function]
  rule func2(4)     => four
  rule func2(_:Int) => seven  [owise]

  syntax S ::= func3(Int)     [function]
  rule func3(X:Int) => four
    requires X >=Int 4        [priority(30)]
  rule func3(X:Int) => five
    requires X >Int 4         [priority(23)]
  rule func3(6)     => six
  rule func3(_:Int) => seven  [owise]

  syntax S ::= func4(Int)     [function]
  rule func4(X:Int) => four
    requires func3(X) ==K four
  rule func4(_:Int) => seven  [owise]

  // for priority-1-spec
  syntax KItem ::= runTest  ( S )
                 | doneTest ( S )

  rule runTest ( T ) => doneTest ( T )

endmodule
