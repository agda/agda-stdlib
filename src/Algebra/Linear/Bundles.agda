------------------------------------------------------------------------
-- The Agda standard library
--
-- Some bundles of linear algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Linear.Bundles where

import Algebra.Module.Morphism.Structures as MorphismStructures

open import Algebra        using (CommutativeRing)
open import Algebra.Module using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Bundles
open import Data.List      using (List; foldr)
open import Data.Product
open import Function
open import Level          using (Level; _⊔_; suc)
open import Relation.Binary
open import Relation.Binary.ExtensionalEquivalence
open import Relation.Binary.Reasoning.MultiSetoid

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

-- Abstract vector spaces.
--
-- A "vector space" is a Module with a commutative, homomorphic inner
-- product and a complete set of building blocks for mapping the space.
record VectorSpace
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (mod       : Module ring m ℓm)
  : Set (suc (ℓr ⊔ r ⊔ ℓm ⊔ m)) where

  constructor mkVS

  open CommutativeRing ring renaming (Carrier  to S)   public
  open Module          mod  renaming (Carrierᴹ to V)   public
  open MorphismStructures.ModuleMorphisms mod ⟨module⟩ public

  vscale : (V → S) → V → V
  vscale f = uncurry _*ₗ_ ∘ < f , id >

  vgen : (V → S) → List V → V
  vgen f = foldr (_+ᴹ_ ∘ vscale f) 0ᴹ

  infix 7 _∙_
  field
    _∙_           : V → V → S
    basisSet      : List V
    basisComplete : ∀ {a : V} →
                    a ≈ᴹ vgen (a ∙_) basisSet

    -- ToDo: Can these be unified, by using one of the
    -- existing algebraic structures?
    -- I'm only finding things that are predicated upon: `A → A → A`, or
    -- `A → B`; nothing for: `A → A → B`.
    ∙-comm      : ∀ {a b}     → a ∙ b ≈ b ∙ a
    ∙-distrib-+ : ∀ {a b c}   → a ∙ (b +ᴹ c)    ≈ (a ∙ b) + (a ∙ c)
    ∙-comm-*ₗ   : ∀ {s} {a b} → a ∙ (s *ₗ b)    ≈ s * (a ∙ b)
    ∙-comm-*ᵣ   : ∀ {s} {a b} → a ∙ (b *ᵣ s)    ≈ (a ∙ b) * s  -- Prove.
    ∙-congˡ     : ∀ {a b c}   → b ≈ᴹ c → a ∙ b ≈ a ∙ c
    ∙-congʳ     : ∀ {a b c}   → b ≈ᴹ c → b ∙ a ≈ c ∙ a        -- Prove.
    ∙-idˡ       : ∀ {a}       → 0ᴹ ∙ a ≈ 0#
    ∙-idʳ       : ∀ {a}       → a ∙ 0ᴹ ≈ 0#                    -- Prove.
    ∙-homo-⁻¹    : ∀ {a b}     → a ∙ (-ᴹ b) ≈ - (a ∙ b)

  vscale-cong : ∀ f → Congruent _≈ᴹ_ _≈_ f → Congruent _≈ᴹ_ _≈ᴹ_ (vscale f)
  vscale-cong f f-cong {x} {y} x≈y = begin⟨ ≈ᴹ-setoid ⟩
    vscale f x ≡⟨⟩
    f x *ₗ x   ≈⟨ *ₗ-congʳ (f-cong x≈y) ⟩
    f y *ₗ x   ≈⟨ *ₗ-congˡ x≈y ⟩
    f y *ₗ y   ≡⟨⟩
    vscale f y ∎

  ------------------------------------------------------------------------
  -- Linear maps from vectors to scalars.
  V⊸S = LinearMap mod ⟨module⟩

  -- Equivalent vector generator.
  v : V⊸S → V
  v lm = vgen (LinearMap.f lm) basisSet

  open Setoid (≈ᴸ-setoid mod ⟨module⟩) public using () renaming
    ( _≈_ to _≈ᴸ_
    ; _≉_ to _≉ᴸ_
    )

