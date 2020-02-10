------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between magma-like structures
------------------------------------------------------------------------

-- See Data.Nat.Binary.Properties for examples of how this and similar
-- modules can be used to easily translate properties between types.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Morphism.Structures
open import Relation.Binary.Core

module Algebra.Morphism.MagmaMonomorphism
  {a b ℓ₁ ℓ₂} {M₁ : RawMagma a ℓ₁} {M₂ : RawMagma b ℓ₂} {⟦_⟧}
  (isMagmaMonomorphism : IsMagmaMonomorphism M₁ M₂ ⟦_⟧)
  where

open IsMagmaMonomorphism isMagmaMonomorphism
open RawMagma M₁ renaming (Carrier to A; _≈_ to _≈₁_; _∙_ to _∙_)
open RawMagma M₂ renaming (Carrier to B; _≈_ to _≈₂_; _∙_ to _◦_)

open import Algebra.Structures
open import Algebra.Definitions
open import Data.Product
open import Data.Sum.Base using (inj₁; inj₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Relation.Binary.Morphism.RelMonomorphism isRelMonomorphism as RelMorphism

------------------------------------------------------------------------
-- Properties

module _ (◦-isMagma : IsMagma _≈₂_ _◦_) where

  open IsMagma ◦-isMagma renaming (∙-cong to ◦-cong)
  open SetoidReasoning setoid

  cong : Congruent₂ _≈₁_ _∙_
  cong {x} {y} {u} {v} x≈y u≈v = injective (begin
    ⟦ x ∙ u ⟧      ≈⟨  homo x u ⟩
    ⟦ x ⟧ ◦ ⟦ u ⟧  ≈⟨  ◦-cong (⟦⟧-cong x≈y) (⟦⟧-cong u≈v) ⟩
    ⟦ y ⟧ ◦ ⟦ v ⟧  ≈˘⟨ homo y v ⟩
    ⟦ y ∙ v ⟧      ∎)

  assoc : Associative _≈₂_ _◦_ → Associative _≈₁_ _∙_
  assoc assoc x y z = injective (begin
    ⟦ (x ∙ y) ∙ z ⟧          ≈⟨  homo (x ∙ y) z ⟩
    ⟦ x ∙ y ⟧ ◦ ⟦ z ⟧        ≈⟨  ◦-cong (homo x y) refl ⟩
    (⟦ x ⟧ ◦ ⟦ y ⟧) ◦ ⟦ z ⟧  ≈⟨  assoc ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
    ⟦ x ⟧ ◦ (⟦ y ⟧ ◦ ⟦ z ⟧)  ≈˘⟨ ◦-cong refl (homo y z) ⟩
    ⟦ x ⟧ ◦ ⟦ y ∙ z ⟧        ≈˘⟨ homo x (y ∙ z) ⟩
    ⟦ x ∙ (y ∙ z) ⟧          ∎)

  comm : Commutative _≈₂_ _◦_ → Commutative _≈₁_ _∙_
  comm comm x y = injective (begin
    ⟦ x ∙ y ⟧      ≈⟨  homo x y ⟩
    ⟦ x ⟧ ◦ ⟦ y ⟧  ≈⟨  comm ⟦ x ⟧ ⟦ y ⟧ ⟩
    ⟦ y ⟧ ◦ ⟦ x ⟧  ≈˘⟨ homo y x ⟩
    ⟦ y ∙ x ⟧      ∎)

  idem : Idempotent _≈₂_ _◦_ → Idempotent _≈₁_ _∙_
  idem idem x = injective (begin
    ⟦ x ∙ x ⟧     ≈⟨ homo x x ⟩
    ⟦ x ⟧ ◦ ⟦ x ⟧ ≈⟨ idem ⟦ x ⟧ ⟩
    ⟦ x ⟧         ∎)

  sel : Selective _≈₂_ _◦_ → Selective _≈₁_ _∙_
  sel sel x y with sel ⟦ x ⟧ ⟦ y ⟧
  ... | inj₁ x◦y≈x = inj₁ (injective (begin
    ⟦ x ∙ y ⟧      ≈⟨ homo x y ⟩
    ⟦ x ⟧ ◦ ⟦ y ⟧  ≈⟨ x◦y≈x ⟩
    ⟦ x ⟧          ∎))
  ... | inj₂ x◦y≈y = inj₂ (injective (begin
    ⟦ x ∙ y ⟧      ≈⟨ homo x y ⟩
    ⟦ x ⟧ ◦ ⟦ y ⟧  ≈⟨ x◦y≈y ⟩
    ⟦ y ⟧          ∎))

  cancelˡ : LeftCancellative _≈₂_ _◦_ → LeftCancellative _≈₁_ _∙_
  cancelˡ cancelˡ x {y} {z} x∙y≈x∙z = injective (cancelˡ ⟦ x ⟧ (begin
    ⟦ x ⟧ ◦ ⟦ y ⟧  ≈˘⟨ homo x y ⟩
    ⟦ x ∙ y ⟧      ≈⟨  ⟦⟧-cong x∙y≈x∙z ⟩
    ⟦ x ∙ z ⟧      ≈⟨  homo x z ⟩
    ⟦ x ⟧ ◦ ⟦ z ⟧  ∎))

  cancelʳ : RightCancellative _≈₂_ _◦_ → RightCancellative _≈₁_ _∙_
  cancelʳ cancelʳ {x} y z y∙x≈z∙x = injective (cancelʳ ⟦ y ⟧ ⟦ z ⟧ (begin
    ⟦ y ⟧ ◦ ⟦ x ⟧  ≈˘⟨ homo y x ⟩
    ⟦ y ∙ x ⟧      ≈⟨  ⟦⟧-cong y∙x≈z∙x ⟩
    ⟦ z ∙ x ⟧      ≈⟨  homo z x ⟩
    ⟦ z ⟧ ◦ ⟦ x ⟧  ∎))

  cancel : Cancellative _≈₂_ _◦_ → Cancellative _≈₁_ _∙_
  cancel = map cancelˡ cancelʳ

------------------------------------------------------------------------
-- Structures

isMagma : IsMagma _≈₂_ _◦_ → IsMagma _≈₁_ _∙_
isMagma isMagma = record
  { isEquivalence = RelMorphism.isEquivalence M.isEquivalence
  ; ∙-cong        = cong isMagma
  } where module M = IsMagma isMagma

isSemigroup : IsSemigroup _≈₂_ _◦_ → IsSemigroup _≈₁_ _∙_
isSemigroup isSemigroup = record
  { isMagma = isMagma S.isMagma
  ; assoc   = assoc   S.isMagma S.assoc
  } where module S = IsSemigroup isSemigroup

isBand : IsBand _≈₂_ _◦_ → IsBand _≈₁_ _∙_
isBand isBand = record
  { isSemigroup = isSemigroup B.isSemigroup
  ; idem        = idem        B.isMagma B.idem
  } where module B = IsBand isBand

isSemilattice : IsSemilattice _≈₂_ _◦_ → IsSemilattice _≈₁_ _∙_
isSemilattice isSemilattice = record
  { isBand = isBand S.isBand
  ; comm   = comm   S.isMagma S.comm
  } where module S = IsSemilattice isSemilattice

isSelectiveMagma : IsSelectiveMagma _≈₂_ _◦_ → IsSelectiveMagma _≈₁_ _∙_
isSelectiveMagma isSelMagma = record
  { isMagma = isMagma S.isMagma
  ; sel     = sel     S.isMagma S.sel
  } where module S = IsSelectiveMagma isSelMagma
