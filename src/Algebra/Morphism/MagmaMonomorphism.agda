------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between magma-like structures
------------------------------------------------------------------------

-- See Data.Nat.Binary.Properties for examples of how this and similar
-- modules can be used to easily translate properties between types.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Algebra.Structures
open import Algebra.Morphism.Structures
open import Relation.Binary.Core

module Algebra.Morphism.MagmaMonomorphism
  {a b} {A : Set a} {B : Set b}
  {ℓ₁ ℓ₂} {_≈₁_ : Rel A ℓ₁} {_≈₂_ : Rel B ℓ₂}
  {_∙_ : Op₂ A} {_◦_ : Op₂ B} {f : A → B}
  (isMagmaMonomorphism : IsMagmaMonomorphism _≈₁_ _≈₂_ _∙_ _◦_ f)
  (◦-isMagma : IsMagma _≈₂_ _◦_)
  where

open IsMagmaMonomorphism isMagmaMonomorphism
open IsMagma ◦-isMagma renaming (∙-cong to ◦-cong)

open import Algebra.Definitions
open import Data.Product
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.Reasoning.Setoid setoid
import Relation.Binary.Morphism.RelMonomorphism isRelMonomorphism as RelMorphism

------------------------------------------------------------------------
-- Properties

cong : Congruent₂ _≈₁_ _∙_
cong {x} {y} {u} {v} x≈y u≈v = injective (begin
  f (x ∙ u) ≈⟨  homo x u ⟩
  f x ◦ f u ≈⟨  ◦-cong (⟦⟧-cong x≈y) (⟦⟧-cong u≈v) ⟩
  f y ◦ f v ≈˘⟨ homo y v ⟩
  f (y ∙ v) ∎)

assoc : Associative _≈₂_ _◦_ → Associative _≈₁_ _∙_
assoc assoc x y z = injective (begin
  f ((x ∙ y) ∙ z)    ≈⟨  homo (x ∙ y) z ⟩
  f (x ∙ y) ◦ f z    ≈⟨  ◦-cong (homo x y) refl ⟩
  (f x ◦ f y) ◦ f z  ≈⟨  assoc (f x) (f y) (f z) ⟩
  f x ◦ (f y ◦ f z)  ≈˘⟨ ◦-cong refl (homo y z) ⟩
  f x ◦ f (y ∙ z)    ≈˘⟨ homo x (y ∙ z) ⟩
  f (x ∙ (y ∙ z))    ∎)

comm : Commutative _≈₂_ _◦_ → Commutative _≈₁_ _∙_
comm comm x y = injective (begin
  f (x ∙ y)  ≈⟨  homo x y ⟩
  f x ◦ f y  ≈⟨  comm (f x) (f y) ⟩
  f y ◦ f x  ≈˘⟨ homo y x ⟩
  f (y ∙ x)  ∎)

idem : Idempotent _≈₂_ _◦_ → Idempotent _≈₁_ _∙_
idem idem x = injective (begin
  f (x ∙ x)  ≈⟨ homo x x ⟩
  f x ◦ f x  ≈⟨ idem (f x) ⟩
  f x        ∎)

sel : Selective _≈₂_ _◦_ → Selective _≈₁_ _∙_
sel sel x y with sel (f x) (f y)
... | inj₁ x◦y≈x = inj₁ (injective (begin
  f (x ∙ y)  ≈⟨ homo x y ⟩
  f x ◦ f y  ≈⟨ x◦y≈x ⟩
  f x        ∎))
... | inj₂ x◦y≈y = inj₂ (injective (begin
  f (x ∙ y)  ≈⟨ homo x y ⟩
  f x ◦ f y  ≈⟨ x◦y≈y ⟩
  f y        ∎))

cancelˡ : LeftCancellative _≈₂_ _◦_ → LeftCancellative _≈₁_ _∙_
cancelˡ cancelˡ x {y} {z} x∙y≈x∙z = injective (cancelˡ (f x) (begin
  f x ◦ f y  ≈˘⟨ homo x y ⟩
  f (x ∙ y)  ≈⟨  ⟦⟧-cong x∙y≈x∙z ⟩
  f (x ∙ z)  ≈⟨  homo x z ⟩
  f x ◦ f z  ∎))

cancelʳ : RightCancellative _≈₂_ _◦_ → RightCancellative _≈₁_ _∙_
cancelʳ cancelʳ {x} y z y∙x≈z∙x = injective (cancelʳ (f y) (f z) (begin
  f y ◦ f x  ≈˘⟨ homo y x ⟩
  f (y ∙ x)  ≈⟨  ⟦⟧-cong y∙x≈z∙x ⟩
  f (z ∙ x)  ≈⟨  homo z x ⟩
  f z ◦ f x  ∎))

cancel : Cancellative _≈₂_ _◦_ → Cancellative _≈₁_ _∙_
cancel = map cancelˡ cancelʳ

------------------------------------------------------------------------
-- Structures

isMagma : IsMagma _≈₁_ _∙_
isMagma = record
  { isEquivalence = RelMorphism.isEquivalence isEquivalence
  ; ∙-cong        = cong
  }

isSemigroup : IsSemigroup _≈₂_ _◦_ → IsSemigroup _≈₁_ _∙_
isSemigroup isSemigroup = record
  { isMagma = isMagma
  ; assoc   = assoc S.assoc
  } where module S = IsSemigroup isSemigroup

isBand : IsBand _≈₂_ _◦_ → IsBand _≈₁_ _∙_
isBand isBand = record
  { isSemigroup = isSemigroup B.isSemigroup
  ; idem        = idem        B.idem
  } where module B = IsBand isBand

isSemilattice : IsSemilattice _≈₂_ _◦_ → IsSemilattice _≈₁_ _∙_
isSemilattice isSemilattice = record
  { isBand = isBand S.isBand
  ; comm   = comm   S.comm
  } where module S = IsSemilattice isSemilattice

isSelectiveMagma : IsSelectiveMagma _≈₂_ _◦_ → IsSelectiveMagma _≈₁_ _∙_
isSelectiveMagma isSelMagma = record
  { isMagma = isMagma
  ; sel     = sel S.sel
  } where module S = IsSelectiveMagma isSelMagma
