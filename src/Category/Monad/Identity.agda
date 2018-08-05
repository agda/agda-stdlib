------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity monad
------------------------------------------------------------------------

module Category.Monad.Identity where

open import Category.Monad
open import Function using (id ; _|>_)

Identity : ∀ {f} → Set f → Set f
Identity A = A

IdentityMonad : ∀ {f} → RawMonad {f} Identity
IdentityMonad = record
  { return = id
  ; _>>=_  = _|>_
  }
