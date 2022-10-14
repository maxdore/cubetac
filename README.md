# cubetac

## Installation

The solver is packaged up with stack, a simple `stack build` should install and
compile everything.

## Usage

The solver can be called on `.cube` files, some examples can be found in
`examples/`. 

A `.cube` file consists of a context and a number of goals. Example:
```
zero : []
one : []
seg : [(zero , one)]
---
app1 = [(seg 1, seg 1) , (zero , one)]
inv = [(one , zero)]
```
The cube has three constructors. The 0-paths `zero` and `one` have an empty
boundary. The 1-path `seg` has one pair of faces as its boundary. The marker
`---` ends the definition of the context and starts the goal section. Each goal
consists of an identifier, we have `app1` and `inv` in this example, and a
boundary prescription after an `=` sign.

The boundary of `app1` consists of 4 faces, so we are describing the boundary of
a square. Each face is implicitly abstracted over a interval variable, which may
be used. For instance, `seg 1` means that we apply that interval variable to the
`seg` path, while `zero` is just a constant path.

A `.cube` can be called with a single goal to be solved. For instance, 

`stack exec cubetac-exe examples/interval.cube app1`

will load the above example and search for a proof of `app1`. The prover can be
asked to give more debugging information by appending a `verbose` as follows:

`stack exec cubetac-exe examples/interval.cube app1 verbose`




## Next steps

Simple solver work for arbitrary dimensions
- boundary check for potential substitutions
- Integrate with Agda

Making representations of types and terms more general
- Extension types
- Partially specified boundaries
- Reversal of paths: Translation between formulas with reversals and partially specified cubes
- Introduce constructors

Kan composition solver
- Implement some basic heuristics:
  - Open squares on top
  - have depth limit
  - congruence closure of hcomps with constructors, search with depth limit (unifier?)

Dependent cubes? Match hosting cube

Integrate with proof search in dependent type theory (Agsy rescuable?)

## Examples

- Loopspaces and simple filling problems in arbitrary dimensions with even number of interval substitutions
- S1 = Susp Bool for constructors around hcomps
- https://github.com/agda/cubical/blob/master/Cubical/HITs/James/Inductive/Coherence.agda
- Smash product:
  - ...
  - pentagon!


