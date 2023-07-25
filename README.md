# [sine-nomine](https://github.com/tweag/bibliotheca-sine-nomine)

Copyright Tweag I/O 2023

With `sine-nomine` you can generate variations of sequences monadic actions.
The main application is generating test cases for stateful systems. 

You are free to copy, modify, and distribute `sine-nomine` under the terms of
the MIT license. See [LICENSE](./LICENSE) for details.

## Main use case: Testing stateful systems

Testing stateful systems is hard, because the admissible actions at each step
are constrained by the actions taken previously. One approach (taken by
[quickchek-state-machine](https://hackage.haskell.org/package/quickcheck-state-machine)
and similar libraries) is to explicitly model all state transitions that can
happen and somehow use this representation to generate test cases. We think
that this often means duplicating the work (and bugs) of the system that's
being tested. Therefore, this library takes a different approach based on
modifying existing traces. The most common workflow will be this:

- Manually write (or generate by some other means) a number of base test
  cases. These will likely correspond to "normal" uses of the system you're
  testing. Chances are you're writing such tests anyway.

- Define some modifications that apply to individual steps in your base test
  cases. You're completely free to do whatever you want here, as long as it is
  implementable in your base monad: disable a check, tamper some data, repeat
  or omit an action,... Crucially, any single-step modification you apply at
  some step may depend on the state reached after the previous steps. This
  means that there's no need to track of the state of the system you're
  testing: You have direct access to it.

- Use one of our [Logics](./src/Logic) to describe how to deploy single-step
  modifications throughout the base test cases. This turns one base test case
  into a description potentially many test cases that have single-step
  modifications applied at strategically chosen positions.

- Run many modified versions of the base test cases, and test some properties
  of their end states. Because you understand the base scenarios and the
  modifications, it's pretty straightforward in most cases to formulate what
  you expect, even if you don't know  the precise details of each generated
  test scenario (and can't know, without running it). Often, you'll just expect
  that successfully applying any single-step modification leads to an error
  (immediately or later on): If it doesn't, the system you're testing doesn't
  catch a deviation from the "allowed" path. 

There are tutorials in [Examples](./src/Examples). The simplest is
[Examples.Ltl.Simple](./src/Examples/Ltl/Simple.hs).

## Documentation

The haddock documentation for current `main` can be seen at
[tweag.github.io/bibliotheca-sine-nomine](https://tweag.github.io/bibliotheca-sine-nomine).
We also direct you to the [examples](./src/Examples).

## Contributing

Issues and Pull Requests welcome! We provide a development environment through
Nix, which also installs the required linting, formatting, and packaging checks
as pre-commit hooks.
