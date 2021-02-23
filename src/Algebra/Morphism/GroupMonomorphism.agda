------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between group-like structures
------------------------------------------------------------------------

-- See Data.Nat.Binary.Properties for examples of how this and similar
-- modules can be used to easily translate properties between types.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles
open import Algebra.Morphism.Structures
open import Relation.Binary.Core

module Algebra.Morphism.GroupMonomorphism
  {a b ℓ₁ ℓ₂} {G₁ : RawGroup a ℓ₁} {G₂ : RawGroup b ℓ₂} {⟦_⟧}
  (isGroupMonomorphism : IsGroupMonomorphism G₁ G₂ ⟦_⟧)
  where

open IsGroupMonomorphism isGroupMonomorphism
open RawGroup G₁ renaming
  (Carrier to A; _≈_ to _≈₁_; _∙_ to _∙_; _⁻¹ to _⁻¹₁; ε to ε₁)
open RawGroup G₂ renaming
  (Carrier to B; _≈_ to _≈₂_; _∙_ to _◦_; _⁻¹ to _⁻¹₂; ε to ε₂)

open import Algebra.Definitions
open import Algebra.Structures
open import Data.Product
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

------------------------------------------------------------------------
-- Re-export all properties of monoid monomorphisms

open import Algebra.Morphism.MonoidMonomorphism
  isMonoidMonomorphism public

------------------------------------------------------------------------
-- Properties

module _ (◦-isMagma : IsMagma _≈₂_ _◦_) where

  open IsMagma ◦-isMagma renaming (∙-cong to ◦-cong)
  open SetoidReasoning setoid

  inverseˡ : LeftInverse _≈₂_ ε₂ _⁻¹₂ _◦_ → LeftInverse _≈₁_ ε₁ _⁻¹₁  _∙_
  inverseˡ invˡ x = injective (begin
    ⟦ x ⁻¹₁ ∙ x ⟧     ≈⟨ ∙-homo (x ⁻¹₁ ) x ⟩
    ⟦ x ⁻¹₁ ⟧ ◦ ⟦ x ⟧ ≈⟨ ◦-cong (⁻¹-homo x) refl ⟩
    ⟦ x ⟧ ⁻¹₂ ◦ ⟦ x ⟧ ≈⟨ invˡ ⟦ x ⟧ ⟩
    ε₂                ≈˘⟨ ε-homo ⟩
    ⟦ ε₁ ⟧ ∎)

  inverseʳ : RightInverse _≈₂_ ε₂ _⁻¹₂ _◦_ → RightInverse _≈₁_ ε₁ _⁻¹₁  _∙_
  inverseʳ invʳ x = injective (begin
    ⟦ x ∙ x ⁻¹₁ ⟧     ≈⟨ ∙-homo x (x ⁻¹₁) ⟩
    ⟦ x ⟧ ◦ ⟦ x ⁻¹₁ ⟧ ≈⟨ ◦-cong refl (⁻¹-homo x) ⟩
    ⟦ x ⟧ ◦ ⟦ x ⟧ ⁻¹₂ ≈⟨ invʳ ⟦ x ⟧ ⟩
    ε₂                ≈˘⟨ ε-homo ⟩
    ⟦ ε₁ ⟧ ∎)

  inverse : Inverse _≈₂_ ε₂ _⁻¹₂ _◦_ → Inverse _≈₁_ ε₁ _⁻¹₁  _∙_
  inverse (invˡ , invʳ) = inverseˡ invˡ , inverseʳ invʳ

  ⁻¹-cong : Congruent₁ _≈₂_ _⁻¹₂ → Congruent₁ _≈₁_ _⁻¹₁
  ⁻¹-cong  ⁻¹-cong {x} {y} x≈y = injective (begin
    ⟦ x ⁻¹₁ ⟧ ≈⟨ ⁻¹-homo x ⟩
    ⟦ x ⟧ ⁻¹₂ ≈⟨ ⁻¹-cong (⟦⟧-cong x≈y) ⟩
    ⟦ y ⟧ ⁻¹₂ ≈˘⟨ ⁻¹-homo y ⟩
    ⟦ y ⁻¹₁ ⟧ ∎)

isGroup : IsGroup _≈₂_ _◦_ ε₂ _⁻¹₂ → IsGroup _≈₁_ _∙_ ε₁ _⁻¹₁
isGroup isGroup = record
  { isMonoid = isMonoid G.isMonoid
  ; inverse  = inverse  G.isMagma G.inverse
  ; ⁻¹-cong  = ⁻¹-cong  G.isMagma G.⁻¹-cong
  } where module G = IsGroup isGroup

isAbelianGroup : IsAbelianGroup _≈₂_ _◦_ ε₂ _⁻¹₂ → IsAbelianGroup _≈₁_ _∙_ ε₁ _⁻¹₁
isAbelianGroup isAbelianGroup = record
  { isGroup = isGroup G.isGroup
  ; comm    = comm G.isMagma G.comm
  } where module G = IsAbelianGroup isAbelianGroup
