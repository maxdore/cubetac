# cubetac


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


