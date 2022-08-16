------------------------------------------------------------------------
-- The Agda standard library
--
-- Some linear algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Linear.Structures where

open import Algebra        using (CommutativeRing)
open import Algebra.Module using (Module)
open import Data.List      using (List; foldr)
open import Data.Product
open import Function
open import Level          using (Level; _⊔_; suc)

module _
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (mod       : Module ring m ℓm)
  where

  open CommutativeRing ring renaming (Carrier  to S)
  open Module          mod  renaming (Carrierᴹ to V)

  -- A set of "vectors" forms a basis for a space iff it is complete
  -- under some inner product.
  record BasisFor (_∙_ : V → V → S) : Set (suc (ℓm ⊔ m ⊔ r)) where

    -- Scale a vector according to some reduction function.
    vscale : (V → S) → V → V
    vscale f = uncurry _*ₗ_ ∘ < f , id >

    -- Generate a vector from the basis, according to some reduction function.
    vgen : (V → S) → List V → V
    vgen f = foldr (_+ᴹ_ ∘ vscale f) 0ᴹ

    field
      basisSet      : List V  -- ToDo: List => Foldable Functor
      basisComplete : ∀ {a : V} → a ≈ᴹ vgen (a ∙_) basisSet


  -- A vector space is characterized by an inner product that
  -- satisfies certain properties.
  record IsVectorSpace (_∙_ : V → V → S) : Set (suc (ℓm ⊔ ℓr ⊔ m ⊔ r)) where

    field
      ∙-comm      : ∀ {a b}     → a ∙ b ≈ b ∙ a
      ∙-distrib-+ : ∀ {a b c}   → a ∙ (b +ᴹ c)    ≈ (a ∙ b) + (a ∙ c)
      ∙-comm-*ₗ   : ∀ {s} {a b} → a ∙ (s *ₗ b)    ≈ s * (a ∙ b)
      ∙-comm-*ᵣ   : ∀ {s} {a b} → a ∙ (b *ᵣ s)    ≈ (a ∙ b) * s
      ∙-congˡ     : ∀ {a b c}   → b ≈ᴹ c → a ∙ b ≈ a ∙ c
      ∙-congʳ     : ∀ {a b c}   → b ≈ᴹ c → b ∙ a ≈ c ∙ a
      ∙-idˡ       : ∀ {a}       → 0ᴹ ∙ a ≈ 0#
      ∙-idʳ       : ∀ {a}       → a ∙ 0ᴹ ≈ 0#
      ∙-homo-⁻¹    : ∀ {a b}     → a ∙ (-ᴹ b) ≈ - (a ∙ b)

