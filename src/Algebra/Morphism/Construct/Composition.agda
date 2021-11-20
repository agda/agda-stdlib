------------------------------------------------------------------------
-- The Agda standard library
--
-- The composition of morphisms between algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Algebra.Morphism.Construct.Composition where

open import Algebra.Bundles
open import Algebra.Morphism.Structures
open import Data.Product
open import Function.Base using (_∘_)
import Function.Construct.Composition as Func
open import Level using (Level)
open import Relation.Binary.Morphism.Construct.Composition
open import Relation.Binary.Definitions using (Transitive)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

------------------------------------------------------------------------
-- Magmas

module _ {M₁ : RawMagma a ℓ₁}
         {M₂ : RawMagma b ℓ₂}
         {M₃ : RawMagma c ℓ₃}
         (open RawMagma)
         (≈₃-trans : Transitive (_≈_ M₃))
         {f : Carrier M₁ → Carrier M₂}
         {g : Carrier M₂ → Carrier M₃}
         where

  isMagmaHomomorphism
    : IsMagmaHomomorphism M₁ M₂ f
    → IsMagmaHomomorphism M₂ M₃ g
    → IsMagmaHomomorphism M₁ M₃ (g ∘ f)
  isMagmaHomomorphism f-homo g-homo = record
    { isRelHomomorphism = isRelHomomorphism F.isRelHomomorphism G.isRelHomomorphism
    ; homo              = λ x y → ≈₃-trans (G.⟦⟧-cong (F.homo x y)) (G.homo (f x) (f y))
    } where module F = IsMagmaHomomorphism f-homo; module G = IsMagmaHomomorphism g-homo

  isMagmaMonomorphism
    : IsMagmaMonomorphism M₁ M₂ f
    → IsMagmaMonomorphism M₂ M₃ g
    → IsMagmaMonomorphism M₁ M₃ (g ∘ f)
  isMagmaMonomorphism f-mono g-mono = record
    { isMagmaHomomorphism = isMagmaHomomorphism F.isMagmaHomomorphism G.isMagmaHomomorphism
    ; injective           = F.injective ∘ G.injective
    } where module F = IsMagmaMonomorphism f-mono; module G = IsMagmaMonomorphism g-mono

  isMagmaIsomorphism
    : IsMagmaIsomorphism M₁ M₂ f
    → IsMagmaIsomorphism M₂ M₃ g
    → IsMagmaIsomorphism M₁ M₃ (g ∘ f)
  isMagmaIsomorphism f-iso g-iso = record
    { isMagmaMonomorphism = isMagmaMonomorphism F.isMagmaMonomorphism G.isMagmaMonomorphism
    ; surjective          = Func.surjective (_≈_ M₁) _ _ ≈₃-trans G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsMagmaIsomorphism f-iso; module G = IsMagmaIsomorphism g-iso


------------------------------------------------------------------------
-- Monoids

module _ {M₁ : RawMonoid a ℓ₁}
         {M₂ : RawMonoid b ℓ₂}
         {M₃ : RawMonoid c ℓ₃}
         (open RawMonoid)
         (≈₃-trans : Transitive (_≈_ M₃))
         {f : Carrier M₁ → Carrier M₂}
         {g : Carrier M₂ → Carrier M₃}
         where

  isMonoidHomomorphism
    : IsMonoidHomomorphism M₁ M₂ f
    → IsMonoidHomomorphism M₂ M₃ g
    → IsMonoidHomomorphism M₁ M₃ (g ∘ f)
  isMonoidHomomorphism f-homo g-homo = record
    { isMagmaHomomorphism = isMagmaHomomorphism ≈₃-trans F.isMagmaHomomorphism G.isMagmaHomomorphism
    ; ε-homo              = ≈₃-trans (G.⟦⟧-cong F.ε-homo) G.ε-homo
    } where module F = IsMonoidHomomorphism f-homo; module G = IsMonoidHomomorphism g-homo

  isMonoidMonomorphism
    : IsMonoidMonomorphism M₁ M₂ f
    → IsMonoidMonomorphism M₂ M₃ g
    → IsMonoidMonomorphism M₁ M₃ (g ∘ f)
  isMonoidMonomorphism f-mono g-mono = record
    { isMonoidHomomorphism = isMonoidHomomorphism F.isMonoidHomomorphism G.isMonoidHomomorphism
    ; injective            = F.injective ∘ G.injective
    } where module F = IsMonoidMonomorphism f-mono; module G = IsMonoidMonomorphism g-mono

  isMonoidIsomorphism
    : IsMonoidIsomorphism M₁ M₂ f
    → IsMonoidIsomorphism M₂ M₃ g
    → IsMonoidIsomorphism M₁ M₃ (g ∘ f)
  isMonoidIsomorphism f-iso g-iso = record
    { isMonoidMonomorphism = isMonoidMonomorphism F.isMonoidMonomorphism G.isMonoidMonomorphism
    ; surjective           = Func.surjective (_≈_ M₁) _ _ ≈₃-trans G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsMonoidIsomorphism f-iso; module G = IsMonoidIsomorphism g-iso


------------------------------------------------------------------------
-- Groups

module _ {G₁ : RawGroup a ℓ₁}
         {G₂ : RawGroup b ℓ₂}
         {G₃ : RawGroup c ℓ₃}
         (open RawGroup)
         (≈₃-trans : Transitive (_≈_ G₃))
         {f : Carrier G₁ → Carrier G₂}
         {g : Carrier G₂ → Carrier G₃}
         where


  isGroupHomomorphism
    : IsGroupHomomorphism G₁ G₂ f
    → IsGroupHomomorphism G₂ G₃ g
    → IsGroupHomomorphism G₁ G₃ (g ∘ f)
  isGroupHomomorphism f-homo g-homo = record
    { isMonoidHomomorphism = isMonoidHomomorphism ≈₃-trans F.isMonoidHomomorphism G.isMonoidHomomorphism
    ; ⁻¹-homo              = λ x → ≈₃-trans (G.⟦⟧-cong (F.⁻¹-homo x)) (G.⁻¹-homo (f x))
    } where module F = IsGroupHomomorphism f-homo; module G = IsGroupHomomorphism g-homo

  isGroupMonomorphism
    : IsGroupMonomorphism G₁ G₂ f
    → IsGroupMonomorphism G₂ G₃ g
    → IsGroupMonomorphism G₁ G₃ (g ∘ f)
  isGroupMonomorphism f-mono g-mono = record
    { isGroupHomomorphism = isGroupHomomorphism F.isGroupHomomorphism G.isGroupHomomorphism
    ; injective           = F.injective ∘ G.injective
    } where module F = IsGroupMonomorphism f-mono; module G = IsGroupMonomorphism g-mono

  isGroupIsomorphism
    : IsGroupIsomorphism G₁ G₂ f
    → IsGroupIsomorphism G₂ G₃ g
    → IsGroupIsomorphism G₁ G₃ (g ∘ f)
  isGroupIsomorphism f-iso g-iso = record
    { isGroupMonomorphism = isGroupMonomorphism F.isGroupMonomorphism G.isGroupMonomorphism
    ; surjective          = Func.surjective (_≈_ G₁) _ _ ≈₃-trans G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsGroupIsomorphism f-iso; module G = IsGroupIsomorphism g-iso


------------------------------------------------------------------------
-- Near semirings

module _ {R₁ : RawNearSemiring a ℓ₁}
         {R₂ : RawNearSemiring b ℓ₂}
         {R₃ : RawNearSemiring c ℓ₃}
         (open RawNearSemiring)
         (≈₃-trans : Transitive (_≈_ R₃))
         {f : Carrier R₁ → Carrier R₂}
         {g : Carrier R₂ → Carrier R₃}
         where

  isNearSemiringHomomorphism
    : IsNearSemiringHomomorphism R₁ R₂ f
    → IsNearSemiringHomomorphism R₂ R₃ g
    → IsNearSemiringHomomorphism R₁ R₃ (g ∘ f)
  isNearSemiringHomomorphism f-homo g-homo = record
    { +-isMonoidHomomorphism = isMonoidHomomorphism ≈₃-trans F.+-isMonoidHomomorphism G.+-isMonoidHomomorphism
    ; *-homo = λ x y → ≈₃-trans (G.⟦⟧-cong (F.*-homo x y)) (G.*-homo (f x) (f y))
    } where module F = IsNearSemiringHomomorphism f-homo; module G = IsNearSemiringHomomorphism g-homo

  isNearSemiringMonomorphism
    : IsNearSemiringMonomorphism R₁ R₂ f
    → IsNearSemiringMonomorphism R₂ R₃ g
    → IsNearSemiringMonomorphism R₁ R₃ (g ∘ f)
  isNearSemiringMonomorphism f-mono g-mono = record
    { isNearSemiringHomomorphism = isNearSemiringHomomorphism F.isNearSemiringHomomorphism G.isNearSemiringHomomorphism
    ; injective                  = F.injective ∘ G.injective
    } where module F = IsNearSemiringMonomorphism f-mono; module G = IsNearSemiringMonomorphism g-mono

  isNearSemiringIsomorphism
    : IsNearSemiringIsomorphism R₁ R₂ f
    → IsNearSemiringIsomorphism R₂ R₃ g
    → IsNearSemiringIsomorphism R₁ R₃ (g ∘ f)
  isNearSemiringIsomorphism f-iso g-iso = record
    { isNearSemiringMonomorphism = isNearSemiringMonomorphism F.isNearSemiringMonomorphism G.isNearSemiringMonomorphism
    ; surjective                 = Func.surjective (_≈_ R₁) _ _ ≈₃-trans G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsNearSemiringIsomorphism f-iso; module G = IsNearSemiringIsomorphism g-iso


------------------------------------------------------------------------
-- Semirings

module _
  {R₁ : RawSemiring a ℓ₁}
  {R₂ : RawSemiring b ℓ₂}
  {R₃ : RawSemiring c ℓ₃}
  (open RawSemiring)
  (≈₃-trans : Transitive (_≈_ R₃))
  {f : Carrier R₁ → Carrier R₂}
  {g : Carrier R₂ → Carrier R₃}
  where


  isSemiringHomomorphism
    : IsSemiringHomomorphism R₁ R₂ f
    → IsSemiringHomomorphism R₂ R₃ g
    → IsSemiringHomomorphism R₁ R₃ (g ∘ f)
  isSemiringHomomorphism f-homo g-homo = record
    { isNearSemiringHomomorphism = isNearSemiringHomomorphism ≈₃-trans F.isNearSemiringHomomorphism G.isNearSemiringHomomorphism
    ; 1#-homo                    = ≈₃-trans (G.⟦⟧-cong F.1#-homo) G.1#-homo
    } where module F = IsSemiringHomomorphism f-homo; module G = IsSemiringHomomorphism g-homo

  isSemiringMonomorphism
    : IsSemiringMonomorphism R₁ R₂ f
    → IsSemiringMonomorphism R₂ R₃ g
    → IsSemiringMonomorphism R₁ R₃ (g ∘ f)
  isSemiringMonomorphism f-mono g-mono = record
    { isSemiringHomomorphism = isSemiringHomomorphism F.isSemiringHomomorphism G.isSemiringHomomorphism
    ; injective              = F.injective ∘ G.injective
    } where module F = IsSemiringMonomorphism f-mono; module G = IsSemiringMonomorphism g-mono

  isSemiringIsomorphism
    : IsSemiringIsomorphism R₁ R₂ f
    → IsSemiringIsomorphism R₂ R₃ g
    → IsSemiringIsomorphism R₁ R₃ (g ∘ f)
  isSemiringIsomorphism f-iso g-iso = record
    { isSemiringMonomorphism = isSemiringMonomorphism F.isSemiringMonomorphism G.isSemiringMonomorphism
    ; surjective             = Func.surjective (_≈_ R₁) _ _ ≈₃-trans G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsSemiringIsomorphism f-iso; module G = IsSemiringIsomorphism g-iso


------------------------------------------------------------------------
-- Rings

module _ {R₁ : RawRing a ℓ₁}
         {R₂ : RawRing b ℓ₂}
         {R₃ : RawRing c ℓ₃}
         (open RawRing)
         (≈₃-trans : Transitive (_≈_ R₃))
         {f : Carrier R₁ → Carrier R₂}
         {g : Carrier R₂ → Carrier R₃}
         where


  isRingHomomorphism
    : IsRingHomomorphism R₁ R₂ f
    → IsRingHomomorphism R₂ R₃ g
    → IsRingHomomorphism R₁ R₃ (g ∘ f)
  isRingHomomorphism f-homo g-homo = record
    { isSemiringHomomorphism = isSemiringHomomorphism ≈₃-trans F.isSemiringHomomorphism G.isSemiringHomomorphism
    ; -‿homo                 = λ x → ≈₃-trans (G.⟦⟧-cong (F.-‿homo x)) (G.-‿homo (f x))
    } where module F = IsRingHomomorphism f-homo; module G = IsRingHomomorphism g-homo

  isRingMonomorphism
    : IsRingMonomorphism R₁ R₂ f
    → IsRingMonomorphism R₂ R₃ g
    → IsRingMonomorphism R₁ R₃ (g ∘ f)
  isRingMonomorphism f-mono g-mono = record
    { isRingHomomorphism = isRingHomomorphism F.isRingHomomorphism G.isRingHomomorphism
    ; injective = F.injective ∘ G.injective
    } where module F = IsRingMonomorphism f-mono;  module G = IsRingMonomorphism g-mono

  isRingIsomorphism
    : IsRingIsomorphism R₁ R₂ f
    → IsRingIsomorphism R₂ R₃ g
    → IsRingIsomorphism R₁ R₃ (g ∘ f)
  isRingIsomorphism f-iso g-iso = record
    { isRingMonomorphism = isRingMonomorphism F.isRingMonomorphism G.isRingMonomorphism
    ; surjective         = Func.surjective (_≈_ R₁) _ _ ≈₃-trans G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsRingIsomorphism f-iso; module G = IsRingIsomorphism g-iso
