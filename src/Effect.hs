-- | The user-facing API of our effect system
module Effect
  ( -- * Effect types
    Effect,
    EffectInject,

    -- * Abstract syntax trees
    AST,

    -- * Interpreting abstract syntax trees
    InterpretEffect (..),
    InterpretEffects,
    interpretAST,

    -- * Interpreting abstract syntax trees, statefully
    InterpretEffectStateful (..),
    InterpretEffectsStateful,
    interpretASTStateful,
  )
where

import Effect.Internal
