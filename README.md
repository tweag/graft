# [sine-nomine](https://github.com/tweag/bibliotheca-sine-nomine)

Copyright Tweag I/O 2023

With `sine-nomine` you can generate variations of sequences of monadic
actions. The main application is deriving test cases for stateful
systems by altering regular scenarios in ways that can depend on the
state.

The monadic actions can take very general shapes, since the library
also understands higher-order operations that "nest" sequences of
actions in one action (like, for example, `catchError :: m a -> (e -> m
a) -> m a`).

## Testing stateful monadic systems

Testing stateful monadic systems is hard, because the admissible
actions at each step might be constrained by the current state
resulting from previous actions. One approach (taken by
[quickchek-state-machine](https://hackage.haskell.org/package/quickcheck-state-machine)
and similar libraries) is to explicitly model all actions that can
happen and use this representation to generate test cases from
scratch. While this bears results in practice, we think that this
often means duplicating work between the system being tested and the
testing engine itself, as both will somehow need to keep track of
relevant state information. This library proposes a different approach
by interfacing with the system directly to use its state while
tampering with existing actions.

## An example of the most common workflow

The most common workflow is showcased in our
[Ltl.Simple](./src/Example/Ltl.Simple.hs) tutorial. It resembles the
following:
- Capture the behavior of your system through a type class of
  monads. This should exhibit the various operations that will be
  available to interact with the system.
- Manually write (or generate by some other means) a number of base
  test cases. These will take the shape of a serie of monadic
  operations, and will likely correspond to "normal" uses of the
  system you're testing. Chances are you're writing such tests anyway.
- Have the effects associated with your domain automatically generated
  for you. They will correspond to abtract representation of
  operations which will allow for state-aware modifications.
- Define a datatype representing the single step modifications to be
  applied on your domain operations. You're completely free to do
  whatever you want here, as long as it is implementable in your base
  monad: disable a check, tamper some data, repeat or omit an
  action,...
- Define a function to explicit how the single-step modifications
  should be interpreted when applied to the effects associated with
  your domain. Crucially, any single-step modification you apply at
  some step may depend on the state reached after the previous
  steps. This means that there's no need to track of the state of the
  system you're testing: You have direct access to it. 
- Use one of our "[Logics](./src/Logic)" to describe how to deploy
  single-step modifications throughout the base test cases. This turns
  one base test case into potentially many test cases that have
  single-step modifications applied at strategically chosen
  positions.
- Run many modified versions of the base test cases, and test some
  properties of their end states. Because you understand the base
  scenarios and the modifications, it's pretty straightforward in most
  cases to formulate what you expect, even if you don't know the
  precise details of each generated test scenario (and can't know,
  without running it). Often, you'll just expect that successfully
  applying any single-step modification leads to an error (immediately
  or later on): If it doesn't, the system you're testing doesn't catch
  a deviation from the "allowed" path.

## More complex usage

The previous common usage can be extended in many ways:
* more complex logics, including custom ones, can be used
* domains can have nested actions (such as the `Writer` monad) in
  positive positions
* domains can be extended by other domains
* builtin domain operations are provided for standard monads

## Documentation

The haddock documentation for current `main` can be seen at
[tweag.github.io/bibliotheca-sine-nomine](https://tweag.github.io/bibliotheca-sine-nomine).
We also direct you to the [examples](./src/Examples).

## Contributing

Issues and Pull Requests welcome! We provide a development environment
through Nix, which also installs the required linting, formatting, and
packaging checks as pre-commit hooks.

You are free to copy, modify, and distribute `sine-nomine` under the
terms of the MIT license. See [LICENSE](./LICENSE) for details.
