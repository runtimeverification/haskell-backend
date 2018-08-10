This direcory contains some simple K definitions requiring relatively
little effort from the execution engine:

- `function-evaluation-demo`:
  A demo for the evaluation of functions (and nothing else).
- `imp-no-domains`:
  IMP without any builtins and without any conditions on rules.
- `imp-functional-state`:
  IMP with integers and equality on K as builtins,
  but with a state defined as a cons list of assignments, not making use of
  list or map matching.