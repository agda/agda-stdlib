------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive IO: simple bindings to Haskell types and functions
------------------------------------------------------------------------

-- NOTE: the contents of this module should be accessed via `IO`.

{-# OPTIONS --cubical-compatible #-}

module IO.Primitive where

open import Agda.Builtin.IO

------------------------------------------------------------------------
-- The IO monad

open import Agda.Builtin.IO public using (IO)

infixl 1 _>>=_

postulate
  pure : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC pure = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}
{-# COMPILE UHC pure = \_ _ x -> UHC.Agda.Builtins.primReturn x #-}
{-# COMPILE UHC _>>=_  = \_ _ _ _ x y -> UHC.Agda.Builtins.primBind x y #-}
