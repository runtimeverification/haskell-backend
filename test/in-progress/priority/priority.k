module PRIORITY
  imports INT
  imports BOOL

  syntax S ::= "one" | "two" | "three"
  rule one => two [priority(1)]
  rule one => three [priority(2)]
endmodule
