------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive IO: simple bindings to Haskell types and functions
------------------------------------------------------------------------

-- NOTE: the contents of this module should be accessed via `IO`.

{-# OPTIONS --cubical-compatible #-}

module IO.Primitive.Core where

open import Level using (Level)
private
  variable
    a : Level
    A B : Set a

------------------------------------------------------------------------
-- The IO monad

open import Agda.Builtin.IO public
  using (IO)

infixl 1 _>>=_

postulate
  pure : A → IO A
  _>>=_  : IO A → (A → IO B) → IO B

{-# COMPILE GHC pure = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}
{-# COMPILE UHC pure = \_ _ x -> UHC.Agda.Builtins.primReturn x #-}
{-# COMPILE UHC _>>=_  = \_ _ _ _ x y -> UHC.Agda.Builtins.primBind x y #-}

-- Haskell-style alternative syntax
return : A → IO A
return = pure

_>>_ : IO A → IO B → IO B
a >> b = a >>= λ _ → b
