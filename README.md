# [graft](https://github.com/tweag/graft)

Copyright Tweag I/O 2023

With `graft` you can generate variations of sequences of monadic
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
[Ltl.Simple](./src/Example/Ltl.Simple.hs) tutorial. It goes like this: 
- Capture the behaviour of your system through a type class of monads
  containing all the relevant _domain actions_. Macros will define most of the
  rest of the machinery.
- Write a number of base test cases. These sequences of monadic actions will
  correspond to "normal" uses of the system. Chances are such tests already
  exist anyway.
- Define _single-step modifications_ and how they should be interpreted when
  applied to actions. Crucially, single-step modifications are _state-aware_:
  their outcome and applicability at some step may depend on the state reached
  after the previous steps. This means that there's no need to keep track of
  the state of the system you're testing: You have direct access to it. You're
  completely free to do whatever you want here, as long as it is implementable
  in your base monad: disable a check, tamper some data, repeat or omit an
  action,...
- Use one of our "[Logics](./src/Logic)" to turn single-step modifications into
  _composite modifications_ that apply to sequences of actions. With those, you
  can turn one base test case into potentially many test cases that have
  single-step modifications applied at strategically chosen positions.
- Run many modified versions of the base test cases, and test some properties
  of their end states. Since these test cases are obtained using state-aware
  modifications, you can't know their behaviour before running them. However,
  the expected properties will remain easy to formulate with the combined
  understanding of your domain and the single-step modifications. Often, you'll
  just expect that successfully applying any single-step modification leads to
  an error (immediately or later on): If it doesn't, the system you're testing
  doesn't catch a deviation from the "allowed" path. 

## Documentation

The haddock documentation for current `main` can be seen at
[tweag.github.io/graft](https://tweag.github.io/graft).
We also direct you to the [examples](./src/Examples).

## Contributing

Issues and Pull Requests welcome! We provide a development environment
through Nix, which also installs the required linting, formatting, and
packaging checks as pre-commit hooks.

## License

You are free to copy, modify, and distribute `graft` under the
terms of the MIT license. See [LICENSE](./LICENSE) for details.
