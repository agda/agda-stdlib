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
