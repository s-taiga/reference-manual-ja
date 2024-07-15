import Verso.Genre.Manual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "The Lean Language" =>

# Types

## Functions


## Propositions

Propositions are meaningful statements that admit proof. {index}[proposition]
Nonsensical statements are not propositions, but false statements are.
All propositions are classified by `Prop`.

Propositions have the following properties:

: Definitional proof irrelevance

  Any two proofs of the same proposition are completely interchangeable.

: Run-time irrelevance

  Propositions are erased from compiled code.

: Impredicativity

  Propositions may quantify over types from any universe whatsoever.

: Restricted Elimination

  With the exception of singletons, propositions cannot be eliminated into non-proposition types.


## Universes

Types are classified by _universes_. {index}[universe]
Each universe has a {deftech (key:="universe level")}[_level_], {index subterm := "of universe"}[level] which is a natural number.
The `Sort` operator constructs a universe from a given level. {index}[`Sort`]
If the level of a universe is smaller than that of another, the universe itself is said to be smaller.
With the exception of propositions (described later in this chapter), types in a given universe may only quantify over types in smaller universes.
`Sort 0` is the type of propositions, while each `Sort (u + 1)` is a type that describes data.

Every universe is an element of every strictly larger universe, so `Sort 5` includes `Sort 4`.
This means that the following examples are accepted:
```lean
example : Sort 5 := Sort 4
example : Sort 2 := Sort 1
```

On the other hand, `Sort 3` is not an element of `Sort 5`:
```lean error := true name := sort3
example : Sort 5 := Sort 3
```

TODO show output

Similarly, because `Unit` is in `Sort 1`, it is not in `Sort 2`:
```lean
example : Sort 1 := Unit
```
```lean error := true
example : Sort 2 := Unit
```

TODO show output

Because propositions and data are used differently and are governed by different rules, the abbreviations `Type` and `Prop` are provided to make the distinction more convenient.  {index}[`Type`] {index}[`Prop`]
`Type u` is an abbreviation for `Sort (u + 1)`, so `Type 0` is `Sort 1` and `Type 3` is `Sort 4`.
`Type 0` can also be abbreviated `Type`, so `Unit : Type` and `Type : Type 1`.
`Prop` is an abbreviation for `Sort 0`.

### Predicativity

Each universe contains dependent function types, which additionally represent universal quantification and implication.
A function type's universe is determined by the universes of its argument and return types.
The specific rules depend on whether the return type of the function is a proposition.

Functions that return propositions (that is, where the result type of the function is some type in `Prop`) may have argument types in any universe whatsoever, and the function type itself is in `Prop`.
In other words, propositions feature _impredicative_ {index}[impredicative]{index subterm := "impredicative"}[quantification] quantification, because propositions can themselves be statements about all propositions.
For example, proof irrelevance can be written as a proposition that quantifies over all propositions:
```lean
example : Prop := ∀ (P : Prop) (p1 p2 : P), p1 = p2
```

For universes at {tech key:="universe level"}[level] `1` and higher (that is, the `Type u` hierarchy), quantification is {deftech}[_predicative_]. {index}[predicative]{index subterm := "predicative"}[quantification]
For these universes, the universe of a function type is the greater of the argument and return types' universes.

```lean
example (α : Type 1) (β : Type 2) : Type 2 := α → β
example (α : Type 2) (β : Type 1) : Type 2 := α → β
```

This example is not accepted, because `α`'s level is greater than `1`. In other words, the annotated universe is smaller than the function type's universe:
```lean error := true
example (α : Type 2) (β : Type 1) : Type 1 := α → β
```
This example is not accepted because the annotated universe is larger than the function type's universe:
```lean error := true
example (α : Type 2) (β : Type 1) : Type 3 := α → β
```

### Polymorphism

Lean supports _universe polymorphism_, {index subterm:="universe"}[polymorphism] {index}[universe polymorphism] which means that constants defined in the Lean environment can take universe parameters.
These parameters can then be instantiated with universe levels when the constant is used.
Universe parameters are written in curly braces following a dot after a constant name.

When fully explicit, the identity function takes a universe parameter `u`:
```lean
def identity.{u} {α : Sort u} (x : α) : α := x
```

TODO port signature macro from blog genre

```lean
#check id
```

This means that `id` can be applied to types in _any_ universe.
Conceptually speaking, `id` is a schematic definition that defines a family of identity functions, one for each universe.

#### Level Expressions

Levels that occur in a definition are not restricted to just variables.
More complex relationships between universes can be defined using level expressions.


````
Level ::= n                -- Concrete levels
        | u, v             -- Variables
        | Level + n        -- Addition of constants
        | max Level Level  -- Least upper bound
        | imax Level Level -- Impredicative LUB
````

Given an assignment of level variables to concrete numbers, evaluating these expressions follows the usual rules of arithmetic.
The `imax` operation is defined as follows:

$``\mathtt{imax}\ u\ v = \begin{cases}{cl}0 & \mathrm{when }v = 0\\\mathtt{max}\ u\ v&\mathrm{otherwise}\end{cases}``

TODO examples

#### Universe Variable Bindings

TODO `universe` command, local universe vars, auto-implicits

#### Unification

TODO injectivity, (defaulting?)



## Inductive Types
