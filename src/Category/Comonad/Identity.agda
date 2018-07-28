------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity comonad
------------------------------------------------------------------------

module Category.Comonad.Identity where

open import Category.Comonad
open import Category.Monad.Identity using (Identity)
open import Function using (id)

comonad : ∀ {f} → RawComonad {f} Identity
comonad = record
  { extract = id
  ; extend  = id
  }
