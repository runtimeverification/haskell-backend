module PATH
  import DOMAINS
  syntax S ::= "a" | "b" | "c" | "d" | "e" | "f"

  rule a    =>  b
  rule a                                    => f

  rule          b   =>  c
  rule          b           =>  d
  rule          b                           => f

  rule                  c   =>  d
  rule                  c                   => f

  rule                          d   =>  e

  rule                                  e   => f
endmodule
/* Everything goes to f but on paths of different lengths
 *
 * a -------------------------> f
 * |  /    /                    ^
 * v /    /                     |
 * b --> c                      |
 *  \    |                     /
 *   \   v                    /
 *    -> d --> e -------------
 */
