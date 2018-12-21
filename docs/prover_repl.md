# Prover REPL

## How to run

Start the REPL with

```
stack exec prover
```

## Supported commands

### Add a formula

```
add <id> : <formula>
```

#### Examples

```
add phi : \implies{#Nat}(#A:#Nat, \implies{#Nat}(#B:#Nat, #A:#Nat))
```

Adds a new formula to the context. `<id>` must be new.

### Add a formula and its proof

```
add <id> : <formula> by <rule>
```

Adds a new formula to the context, together with its proof.
`<id>` must be new.

#### Example

```
add phi1 : \implies{#Nat}(#A:#Nat, \implies{#Nat}(#B:#Nat, #A:#Nat)) by propositional1(#A:#Nat,#B:#Nat)
```

### Prove a formula

```
prove <id> by <rule>
```

Proves the formula identified by `id` using `rule`.
Notice that `id` must already exist in the proof object.

#### Example

First add a formula (as in the example above)

```
add phi : \implies{#Nat}(#A:#Nat, \implies{#Nat}(#B:#Nat, #A:#Nat))
```

then:

```
prove phi by propositional1(#A:#Nat,#B:#Nat)
```

## TODO

See Trello board!
