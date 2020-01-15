module PRIORITY
  imports INT
  imports BOOL

  syntax S ::= "one" | "two" | "three" | "four" | "five" | "six" | "seven"
  rule one => two [priority(1)]
  rule one => three [priority(2)]

  syntax S ::= func1(Int)     [function]
  rule func1(X:Int) => four
    requires X ==Int 4        
  rule func1(4)     => four
  rule func1(X:Int) => seven  [priority(99)] 

  syntax S ::= func2(Int)     [function]
  rule func2(4)     => four   
  rule func2(_:Int) => seven  [owise, priority(1)]

endmodule
