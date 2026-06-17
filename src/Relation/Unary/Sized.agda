------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed unary relations over sized types
------------------------------------------------------------------------

-- Sized types live in the special sort `SizeUniv` and therefore are no
-- longer compatible with the ordinary combinators defined in
-- `Relation.Unary`.

{-# OPTIONS --without-K --sized-types #-}

module Relation.Unary.Sized  where

open import Level
open import Size

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

infixr 8 _⇒_
_⇒_ : SizedSet ℓ₁ → SizedSet ℓ₂ → SizedSet (ℓ₁ ⊔ ℓ₂)
F ⇒ G = λ i → F i → G i

∀[_] : SizedSet ℓ → Set ℓ
∀[ F ] = ∀{i} → F i
