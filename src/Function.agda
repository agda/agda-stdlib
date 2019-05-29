------------------------------------------------------------------------
-- The Agda standard library
--
-- Functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Note that it is not necessary to provide the equality relations. If
-- not provided then the only change is that it is necessary to provide
-- them when using the contents of `Function.Definitions` and
-- `Function.Structures`.

open import Relation.Binary using (Rel)

module Function
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
  (_≈₁_ : Rel A ℓ₁) -- Equality over the domain
  (_≈₂_ : Rel B ℓ₂) -- Equality over the codomain
  where

open import Function.Core public
open import Function.Definitions _≈₁_ _≈₂_ public
open import Function.Structures _≈₁_ _≈₂_ public
open import Function.Packages public
