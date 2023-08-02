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

## An example of the most common workflow

The most common workflow will be this:

- Capture the behavior of your system through a type class of monads. This should exhibit the various action that will be possible to interact with the system. Here is an example of actions expected to interact with a key-value-store.

``` haskell
class (Monad m) => MonadKeyValue k v m where
  storeValue :: k -> v -> m ()
  getValue :: k -> m (Maybe v)
  deleteValue :: k -> m ()
```

- Manually write (or generate by some other means) a number of base test
  cases. These will likely correspond to "normal" uses of the system you're
  testing. Chances are you're writing such tests anyway. Here is a example of scenario:
  
``` haskell
trace :: (MonadKeyValue Integer String m) => m ()
trace = do
  storeValue 1 "a"
  deleteValue @_ @String 1
  storeValue 1 "b"
```

- Define some modifications that apply to individual steps in your base test
  cases. You're completely free to do whatever you want here, as long as it is
  implementable in your base monad: disable a check, tamper some data, repeat
  or omit an action,... Crucially, any single-step modification you apply at
  some step may depend on the state reached after the previous steps. This
  means that there's no need to track of the state of the system you're
  testing: You have direct access to it. Here is a modification with a single
  constructor. It will be given a meaning further on.

``` haskell
data SingleStepMod = ConcatIfReplace
```

- Use one of our [Logics](./src/Logic) to describe how to deploy single-step
  modifications throughout the base test cases. This turns one base test case
  into potentially many test cases that have single-step
  modifications applied at strategically chosen positions. Here we give a meaning
  of our modification through how to interprete it when deployed on a 
  specific subset of linear temporal logic. As the name suggest, we make it
  so that store concatenates old and new strings.
  
``` haskell
instance (Semigroup v, MonadKeyValue k v m) => InterpretLtl SingleStepMod m (KeyValueEffect k v) where
  interpretLtl (StoreValue key val) = Apply $ \ConcatIfReplace -> do
    mv <- getValue @k @v key
    case mv of
      Just oldVal -> storeValue key (oldVal <> val) >> return (Just ())
      Nothing -> return Nothing
  interpretLtl _ = Ignore
```

- Run many modified versions of the base test cases, and test some properties
  of their end states. Because you understand the base scenarios and the
  modifications, it's pretty straightforward in most cases to formulate what
  you expect, even if you don't know  the precise details of each generated
  test scenario (and can't know, without running it). Often, you'll just expect
  that successfully applying any single-step modification leads to an error
  (immediately or later on): If it doesn't, the system you're testing doesn't
  catch a deviation from the "allowed" path. 

``` haskell
example :: [((), Map Integer String)]
example =
  interpretAndRun
    mempty
    (modifyLtl (somewhere ConcatIfReplace) bugTrace)
```

Here we attempt to create a variation of `trace` for each position where it is applicable. In practice, in should be applicable once (for the second storage) but, depending on your concrete implementation (let's say `deleteValue` does not actually delete properly) it might not be applicable anywhere, which could uncover a bug.

## More complex usage

The previous common usage can be extended in many ways:
* more complexe logics, including custom ones, can be used
* domains can have nested actions (such as the `Writer` monad) 
* domains can be extended
* builtin domain operations are provided for standard monads

## Tutorials and examples

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
