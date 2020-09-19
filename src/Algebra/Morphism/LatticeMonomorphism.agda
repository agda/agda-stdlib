------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between lattice-like structures
------------------------------------------------------------------------

-- See Data.Nat.Binary.Properties for examples of how this and similar
-- modules can be used to easily translate properties between types.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Morphism.Structures
open import Relation.Binary.Core

module Algebra.Morphism.LatticeMonomorphism
  {a b ℓ₁ ℓ₂} {L₁ : RawLattice a ℓ₁} {L₂ : RawLattice b ℓ₂} {⟦_⟧}
  (isLatticeMonomorphism : IsLatticeMonomorphism L₁ L₂ ⟦_⟧)
  where

open IsLatticeMonomorphism isLatticeMonomorphism
open RawLattice L₁ renaming (Carrier to A; _≈_ to _≈₁_; _∨_ to _∨_; _∧_ to _∧_)
open RawLattice L₂ renaming (Carrier to B; _≈_ to _≈₂_; _∨_ to _⊔_; _∧_ to _⊓_)

open import Algebra.Structures
open import Algebra.Definitions
open import Algebra.Properties.Lattice
open import Data.Product
open import Data.Sum.Base using (inj₁; inj₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Relation.Binary.Morphism.RelMonomorphism (∨.IsMagmaMonomorphism.isRelMonomorphism L₁ L₂ ∨-isMagmaMonomorphism) as RelMorphism

------------------------------------------------------------------------
-- Re-export all properties of magma monomorphisms

open import Algebra.Morphism.MagmaMonomorphism ∨-isMagmaMonomorphism using () renaming
  ( cong to ∨-cong
  ; assoc to ∨-assoc
  ; comm to ∨-comm
  ; idem to ∨-idem
  ; sel to ∨-sel
  ; cancelˡ to ∨-cancelˡ
  ; cancelʳ to ∨-cancelʳ
  ; cancel to ∨-cancel
  )

open import Algebra.Morphism.MagmaMonomorphism ∧-isMagmaMonomorphism using () renaming
  ( cong to ∧-cong
  ; assoc to ∧-assoc
  ; comm to ∧-comm
  ; idem to ∧-idem
  ; sel to ∧-sel
  ; cancelˡ to ∧-cancelˡ
  ; cancelʳ to ∧-cancelʳ
  ; cancel to ∧-cancel
  )

------------------------------------------------------------------------
-- Properties

module _ (⊔-⊓-isLattice : IsLattice _≈₂_ _⊔_ _⊓_) where

  open IsLattice ⊔-⊓-isLattice using (isEquivalence) renaming
    ( ∨-congˡ to ⊔-congˡ
    ; ∨-congʳ to ⊔-congʳ
    ; ∧-cong to ⊓-cong
    ; ∧-congˡ to ⊓-congˡ
    ; ∨-absorbs-∧ to ⊔-absorbs-⊓
    ; ∧-absorbs-∨ to ⊓-absorbs-⊔
    )
  open SetoidReasoning (record { isEquivalence = isEquivalence })

  ∨-absorbs-∧ : _Absorbs_ _≈₁_ _∨_ _∧_
  ∨-absorbs-∧ x y = injective (begin
    ⟦ x ∨ x ∧ y ⟧                        ≈⟨ ∨-homo x (x ∧ y) ⟩
    ⟦ x ⟧ ⊔ ⟦ x ∧ y ⟧                    ≈⟨ ⊔-congˡ (∧-homo x y) ⟩
    ⟦ x ⟧ ⊔ ⟦ x ⟧ ⊓ ⟦ y ⟧                ≈⟨ ⊔-absorbs-⊓ ⟦ x ⟧ ⟦ y ⟧ ⟩
    ⟦ x ⟧                                ∎)

  ∧-absorbs-∨ : _Absorbs_ _≈₁_ _∧_ _∨_
  ∧-absorbs-∨ x y = injective (begin
    ⟦ x ∧ (x ∨ y) ⟧                      ≈⟨ ∧-homo x (x ∨ y) ⟩
    ⟦ x ⟧ ⊓ ⟦ x ∨ y ⟧                    ≈⟨ ⊓-congˡ (∨-homo x y) ⟩
    ⟦ x ⟧ ⊓ (⟦ x ⟧ ⊔ ⟦ y ⟧)              ≈⟨ ⊓-absorbs-⊔ ⟦ x ⟧ ⟦ y ⟧ ⟩
    ⟦ x ⟧                                ∎)

  absorptive : Absorptive _≈₁_ _∨_ _∧_
  absorptive = ∨-absorbs-∧ , ∧-absorbs-∨

  distribʳ : _DistributesOverʳ_ _≈₂_ _⊔_ _⊓_ → _DistributesOverʳ_ _≈₁_ _∨_ _∧_
  distribʳ distribʳ x y z = injective (begin
    ⟦ y ∧ z ∨ x ⟧                        ≈⟨ ∨-homo (y ∧ z) x ⟩
    ⟦ y ∧ z ⟧ ⊔ ⟦ x ⟧                    ≈⟨ ⊔-congʳ (∧-homo y z) ⟩
    ⟦ y ⟧ ⊓ ⟦ z ⟧ ⊔ ⟦ x ⟧                ≈⟨ distribʳ ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
    (⟦ y ⟧ ⊔ ⟦ x ⟧) ⊓ (⟦ z ⟧ ⊔ ⟦ x ⟧)    ≈˘⟨ ⊓-cong (∨-homo y x) (∨-homo z x) ⟩
    ⟦ y ∨ x ⟧ ⊓ ⟦ z ∨ x ⟧                ≈˘⟨ ∧-homo (y ∨ x) (z ∨ x) ⟩
    ⟦ (y ∨ x) ∧ (z ∨ x) ⟧                ∎)

isLattice : IsLattice _≈₂_ _⊔_ _⊓_ → IsLattice _≈₁_ _∨_ _∧_
isLattice isLattice = record
  { isEquivalence = RelMorphism.isEquivalence (IsLattice.isEquivalence isLattice)
  ; ∨-comm = ∨-comm (∨-isMagma lattice) (IsLattice.∨-comm isLattice)
  ; ∨-assoc = ∨-assoc (∨-isMagma lattice) (IsLattice.∨-assoc isLattice)
  ; ∨-cong = ∨-cong (∨-isMagma lattice)
  ; ∧-comm = ∧-comm (∧-isMagma lattice) (IsLattice.∧-comm isLattice)
  ; ∧-assoc = ∧-assoc (∧-isMagma lattice) (IsLattice.∧-assoc isLattice)
  ; ∧-cong = ∧-cong (∧-isMagma lattice)
  ; absorptive = absorptive isLattice
  } where
    lattice : Lattice _ _
    lattice = record { isLattice = isLattice }

isDistributiveLattice : IsDistributiveLattice _≈₂_ _⊔_ _⊓_ → IsDistributiveLattice _≈₁_ _∨_ _∧_
isDistributiveLattice isDistributiveLattice = record
  { isLattice = isLattice (IsDistributiveLattice.isLattice isDistributiveLattice)
  ; ∨-distribʳ-∧ = distribʳ (IsDistributiveLattice.isLattice isDistributiveLattice) (IsDistributiveLattice.∨-distribʳ-∧ isDistributiveLattice)
  }

