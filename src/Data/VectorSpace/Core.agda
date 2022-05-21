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
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  -- (mod       : Module ring r ℓr)
  (mod       : Module ring m ℓm)
  where

  open CommutativeRing ring renaming (Carrier  to S)  -- "S" for scalar.
  open Module          mod  renaming (Carrierᴹ to T)  -- "T" for tensor.
    
  -- record VectorSpace : Set (suc (ℓr ⊔ r)) where
  record VectorSpace : Set (suc (ℓr ⊔ r ⊔ ℓm ⊔ m)) where

    constructor mkVS
    infix 7 _∙_
    field
      _∙_           : T → T → S
      basisSet      : List T
      basisComplete : ∀ {a : T} →
                      a ≈ᴹ foldl (λ acc b → acc +ᴹ (a ∙ b) *ₗ b) 0ᴹ basisSet
      -- ToDo: Can these be unified, by using one of the
      -- existing algebraic structures?
      -- I'm only finding things that are predicated upon: `A → A → A`, or
      -- `A → B`; nothing for: `A → A → B`.
      comm-∙        : ∀ {a b : T} → a ∙ b ≈ b ∙ a
      ∙-distrib-+   : ∀ {a b c : T} → a ∙ (b +ᴹ c) ≈ (a ∙ b) + (a ∙ c)
      ∙-comm-*ₗ     : ∀ {s : S} {a b : T} → a ∙ (s *ₗ b) ≈ s * (a ∙ b)
      ∙-congˡ       : ∀ {a b c} → b ≈ᴹ c → a ∙ b ≈ a ∙ c
      ∙-congʳ       : ∀ {a b c} → b ≈ᴹ c → b ∙ a ≈ c ∙ a  -- Prove.
      ∙-idˡ         : ∀ {a : T} → 0ᴹ ∙ a ≈ 0#
      ∙-idʳ         : ∀ {a : T} → a ∙ 0ᴹ ≈ 0#              -- Prove.

