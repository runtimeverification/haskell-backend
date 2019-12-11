require "adomains.k"
require "state.k"

module ASTATE
  imports STATE-BASIC
  imports AID

  syntax StateKey ::= AId

  syntax State ::= #set(Assignment, State, StateKey, StateValue, Bool) [function]
  rule set((K:AId |-> V:StateValue) S:State, K':AId, V':StateValue)
       => #set((K |-> V), S, K', V', K =/=AId K')
  rule #set(A:Assignment, S:State, K':AId, V':StateValue, true)
       => A set(S, K', V')
  rule #set(_:Assignment, S:State, K:AId, V:StateValue, false)
       => (K |-> V) S

  syntax Bool ::= #inState(State, StateKey, Bool) [function]
  rule inState((K:AId |-> _:StateValue) S:State, K':AId)
       => #inState(S, K', K =/=AId K')
  rule #inState(S:State, K':AId, true)
       => inState(S, K')
  rule #inState(S:State, _:AId, false)
       => true

  syntax StateValue ::= #get(StateValue, State, StateKey, Bool) [function, partial]
  rule get((K:AId |-> V:StateValue) S:State, K':AId)
       => #get(V, S, K', K =/=AId K')
  rule #get(_:StateValue, S:State, K:AId, true)
       => get(S, K)
  rule #get(V:StateValue, S:State, _:AId, false)
       => V
endmodule