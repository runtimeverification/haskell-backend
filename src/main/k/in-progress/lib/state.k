module STATE-API
  imports BOOL

  syntax StateKey
  syntax StateValue

  syntax Assignment
    ::= StateKey "|->" StateValue

  syntax State
    ::= ".State" | Assignment State

  syntax State ::= set(State, StateKey, StateValue) [function]

  syntax Bool ::= inState(State, StateKey) [function]

  syntax StateValue ::= get(State, StateKey) [function, partial]
endmodule

module STATE-BASIC
  imports STATE-API
  rule set(.State, K:StateKey, V:StateValue) => (K |-> V) .State
  rule set((K:StateKey |-> _:StateValue) S:State, K:StateKey, V:StateValue)
       => (K |-> V) S

  rule inState(.State, _) => false
  rule inState((K:StateKey |-> _:StateValue) S:State, K:StateKey) => true

  rule get((K:StateKey |-> V:StateValue) S:State, K:StateKey) => V
endmodule

module STATE
  imports STATE-BASIC
  imports K-EQUAL

  rule set((K:StateKey |-> V:StateValue) S:State, K':StateKey, V':StateValue)
       => (K |-> V) set(S, K', V')
       requires K =/=K K'

  rule inState((K:StateKey |-> _:StateValue) S:State, K':StateKey)
       => inState(S, K')
       requires K =/=K K'

  rule get((K:StateKey |-> _:StateValue) S:State, K':StateKey) => get(S, K')
       requires K =/=K K'
endmodule