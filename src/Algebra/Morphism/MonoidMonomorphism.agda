------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between monoid-like structures
------------------------------------------------------------------------

-- See Data.Nat.Binary.Properties for examples of how this and similar
-- modules can be used to easily translate properties between types.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles
open import Algebra.Morphism.Structures
open import Relation.Binary.Core

module Algebra.Morphism.MonoidMonomorphism
  {a b ℓ₁ ℓ₂} {M₁ : RawMonoid a ℓ₁} {M₂ : RawMonoid b ℓ₂} {⟦_⟧}
  (isMonoidMonomorphism : IsMonoidMonomorphism M₁ M₂ ⟦_⟧)
  where

open IsMonoidMonomorphism isMonoidMonomorphism
open RawMonoid M₁ renaming (Carrier to A; _≈_ to _≈₁_; _∙_ to _∙_; ε to ε₁)
open RawMonoid M₂ renaming (Carrier to B; _≈_ to _≈₂_; _∙_ to _◦_; ε to ε₂)

open import Algebra.Definitions
open import Algebra.Structures
open import Data.Product using (map)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

------------------------------------------------------------------------
-- Re-export all properties of magma monomorphisms

open import Algebra.Morphism.MagmaMonomorphism
  isMagmaMonomorphism public

------------------------------------------------------------------------
-- Properties

module _ (◦-isMagma : IsMagma _≈₂_ _◦_) where

  open IsMagma ◦-isMagma renaming (∙-cong to ◦-cong)
  open SetoidReasoning setoid

  identityˡ : LeftIdentity _≈₂_ ε₂ _◦_ → LeftIdentity _≈₁_ ε₁ _∙_
  identityˡ idˡ x = injective (begin
    ⟦ ε₁ ∙ x ⟧      ≈⟨ homo ε₁ x ⟩
    ⟦ ε₁ ⟧ ◦ ⟦ x ⟧  ≈⟨ ◦-cong ε-homo refl ⟩
    ε₂ ◦ ⟦ x ⟧      ≈⟨ idˡ ⟦ x ⟧ ⟩
    ⟦ x ⟧           ∎)

  identityʳ : RightIdentity _≈₂_ ε₂ _◦_ → RightIdentity _≈₁_ ε₁ _∙_
  identityʳ idʳ x = injective (begin
    ⟦ x ∙ ε₁ ⟧      ≈⟨ homo x ε₁ ⟩
    ⟦ x ⟧ ◦ ⟦ ε₁ ⟧  ≈⟨ ◦-cong refl ε-homo ⟩
    ⟦ x ⟧ ◦ ε₂      ≈⟨ idʳ ⟦ x ⟧ ⟩
    ⟦ x ⟧           ∎)

  identity : Identity _≈₂_ ε₂ _◦_ → Identity _≈₁_ ε₁ _∙_
  identity = map identityˡ identityʳ

  zeroˡ : LeftZero _≈₂_ ε₂ _◦_ → LeftZero _≈₁_ ε₁ _∙_
  zeroˡ zeˡ x = injective (begin
    ⟦ ε₁ ∙ x ⟧     ≈⟨  homo ε₁ x ⟩
    ⟦ ε₁ ⟧ ◦ ⟦ x ⟧ ≈⟨  ◦-cong ε-homo refl ⟩
    ε₂   ◦ ⟦ x ⟧   ≈⟨  zeˡ ⟦ x ⟧ ⟩
    ε₂             ≈˘⟨ ε-homo ⟩
    ⟦ ε₁ ⟧         ∎)

  zeroʳ : RightZero _≈₂_ ε₂ _◦_ → RightZero _≈₁_ ε₁ _∙_
  zeroʳ zeʳ x = injective (begin
    ⟦ x ∙ ε₁ ⟧     ≈⟨  homo x ε₁ ⟩
    ⟦ x ⟧ ◦ ⟦ ε₁ ⟧ ≈⟨  ◦-cong refl ε-homo ⟩
    ⟦ x ⟧ ◦ ε₂     ≈⟨  zeʳ ⟦ x ⟧ ⟩
    ε₂             ≈˘⟨ ε-homo ⟩
    ⟦ ε₁ ⟧         ∎)

  zero : Zero _≈₂_ ε₂ _◦_ → Zero _≈₁_ ε₁ _∙_
  zero = map zeroˡ zeroʳ

------------------------------------------------------------------------
-- Structures

isMonoid : IsMonoid _≈₂_ _◦_ ε₂ → IsMonoid _≈₁_ _∙_ ε₁
isMonoid isMonoid = record
  { isSemigroup = isSemigroup M.isSemigroup
  ; identity    = identity    M.isMagma M.identity
  } where module M = IsMonoid isMonoid

isCommutativeMonoid : IsCommutativeMonoid _≈₂_ _◦_ ε₂ →
                      IsCommutativeMonoid _≈₁_ _∙_ ε₁
isCommutativeMonoid isCommMonoid = record
  { isMonoid = isMonoid C.isMonoid
  ; comm     = comm     C.isMagma C.comm
  } where module C = IsCommutativeMonoid isCommMonoid
