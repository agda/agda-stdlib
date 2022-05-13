------------------------------------------------------------------------
-- The Agda standard library
--
-- Abstract vector spaces.
--
-- A "vector space" is a Module with a commutative, homomorphic inner
-- product and a complete set of "building blocks" for mapping the space.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.VectorSpace.Core where

open import Algebra        using (CommutativeRing)
open import Algebra.Module using (Module)
open import Data.List      using (List; foldl)
open import Level          using (Level; _⊔_; suc)

module _
  {r ℓr : Level}
  {ring      : CommutativeRing r ℓr}
  (mod       : Module ring r ℓr)
  where

  open CommutativeRing ring
    using (_+_; _*_; _≈_) renaming
    ( Carrier  to S     -- "S" for scalar.
    )
  open Module mod
    using () renaming
    ( Carrierᴹ to T     -- "T" for tensor.
    ; _+ᴹ_     to _+ᵀ_
    ; _*ₗ_     to _·_
    ; _≈ᴹ_     to _≈ᵀ_
    ; 0ᴹ       to 0ᵀ
    )
    
  record VectorSpace : Set (suc (ℓr ⊔ r)) where

    constructor mkVS
    infix 7 _∘_
    field
      _∘_           : T → T → S
      comm-∘        : ∀ {a b : T} → a ∘ b ≈ b ∘ a
      ∘-distrib-+   : ∀ {a b c : T} → a ∘ (b +ᵀ c) ≈ (a ∘ b) + (a ∘ c)
      ∘-comm-·      : ∀ {s : S} {a b : T} → a ∘ (s · b) ≈ s * (a ∘ b)
      basisSet      : List T
      basisComplete : ∀ {a : T} →
                      a ≈ᵀ foldl (λ acc b → acc +ᵀ (a ∘ b) · b) 0ᵀ basisSet

