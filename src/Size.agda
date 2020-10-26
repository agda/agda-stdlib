------------------------------------------------------------------------
-- The Agda standard library
--
-- Sizes for Agda's sized types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Size where

open import Agda.Builtin.Size public
  using ( SizeUniv            --  sort SizeUniv
        ; Size                --  Size   : SizeUniv
        ; Size<_              --  Size<_ : Size → SizeUniv
        ; ↑_                  --  ↑_     : Size → Size
        ; _⊔ˢ_                --  _⊔ˢ_   : Size → Size → Size
        ; ∞                   --  ∞      : Size
        )

open import Level

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

-- Concept of sized type

SizedType : (ℓ : Level) → Set (suc ℓ)
SizedType ℓ = Size → Set ℓ

-- Type constructors involving SizedType

module SizedType where

  infixr 8 _⇒_

  _⇒_ : SizedType ℓ₁ → SizedType ℓ₂ → SizedType (ℓ₁ ⊔ ℓ₂)
  F ⇒ G = λ i → F i → G i

  ∀[_] : SizedType ℓ → Set ℓ
  ∀[ F ] = ∀{i} → F i
