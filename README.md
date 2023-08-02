# [sine-nomine](https://github.com/tweag/bibliotheca-sine-nomine)

Copyright Tweag I/O 2023

With `sine-nomine` you can generate variations of sequences of -- possibly nested -- monadic actions.
The main application is deriving test cases for stateful systems by tampering with regular scenarios.

You are free to copy, modify, and distribute `sine-nomine` under the terms of
the MIT license. See [LICENSE](./LICENSE) for details.

## Testing stateful monadic systems

Testing stateful monadic systems is hard, because the admissible actions at each step
might be constrained by the current state resulting from previous actions. One approach (taken by
[quickchek-state-machine](https://hackage.haskell.org/package/quickcheck-state-machine)
and similar libraries) is to explicitly model all actions that can
happen and use this representation to generate test cases from scratch. While this bears results in practice,
we think that this often means duplicated work from the system and the testing engine, as both
will somehow need to keep track of relevant state information.
This library proposes a different approach by interfacting with the system directly to
use its state while tampering about existing actions. In practice, this revolves around
modifying existing traces -- sequences of actions -- of the system's execution throughout their execution.

## Most common workflow

The most common workflow will be this:

- Capture the behavior of your system through a type class of monads. This should exhibit the various action that will be possible to interact with the system. Here is an example of actions expected to interact with a key-value-store.

`class (Monad m) => MonadKeyValue k v m where
  storeValue :: k -> v -> m ()
  getValue :: k -> m (Maybe v)
  deleteValue :: k -> m ()`

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
