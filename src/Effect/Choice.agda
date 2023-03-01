------------------------------------------------------------------------
-- The Agda standard library
--
-- Type constructors giving rise to a semigroup at every type
-- e.g. (List, _++_)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Choice where

open import Level

private
  variable
    ℓ ℓ′ : Level
    A  : Set ℓ

record RawChoice (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  infixr 3 _<|>_ _∣_
  field
    _<|>_ : F A → F A → F A

  -- backwards compatibility: unicode variants
  _∣_ : F A → F A → F A
  _∣_ = _<|>_
