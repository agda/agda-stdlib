------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.DistributiveLattice
  {dl₁ dl₂} (DL : DistributiveLattice dl₁ dl₂)
  where

open DistributiveLattice DL
import Algebra.Properties.Lattice as LatticeProperties
open import Algebra.Structures
open import Algebra.FunctionProperties _≈_
open import Relation.Binary
open import Relation.Binary.Reasoning.Setoid setoid
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Data.Product using (_,_)

------------------------------------------------------------------------
-- Export properties of lattices

open LatticeProperties lattice public
  hiding (replace-equality)

------------------------------------------------------------------------
-- Other properties

∨-distribˡ-∧ : _∨_ DistributesOverˡ _∧_
∨-distribˡ-∧ x y z = begin
  x ∨ y ∧ z          ≈⟨ ∨-comm _ _ ⟩
  y ∧ z ∨ x          ≈⟨ ∨-distribʳ-∧ _ _ _ ⟩
  (y ∨ x) ∧ (z ∨ x)  ≈⟨ ∨-comm _ _ ⟨ ∧-cong ⟩ ∨-comm _ _ ⟩
  (x ∨ y) ∧ (x ∨ z)  ∎

∨-distrib-∧ : _∨_ DistributesOver _∧_
∨-distrib-∧ = ∨-distribˡ-∧ , ∨-distribʳ-∧

∧-distribˡ-∨ : _∧_ DistributesOverˡ _∨_
∧-distribˡ-∨ x y z = begin
  x ∧ (y ∨ z)                ≈⟨ ∧-congʳ $ sym (∧-absorbs-∨ _ _) ⟩
  (x ∧ (x ∨ y)) ∧ (y ∨ z)    ≈⟨ ∧-congʳ $ ∧-congˡ $ ∨-comm _ _ ⟩
  (x ∧ (y ∨ x)) ∧ (y ∨ z)    ≈⟨ ∧-assoc _ _ _ ⟩
  x ∧ ((y ∨ x) ∧ (y ∨ z))    ≈⟨ ∧-congˡ $ sym (∨-distribˡ-∧ _ _ _) ⟩
  x ∧ (y ∨ x ∧ z)            ≈⟨ ∧-congʳ $ sym (∨-absorbs-∧ _ _) ⟩
  (x ∨ x ∧ z) ∧ (y ∨ x ∧ z)  ≈⟨ sym $ ∨-distribʳ-∧ _ _ _ ⟩
  x ∧ y ∨ x ∧ z              ∎

∧-distribʳ-∨ : _∧_ DistributesOverʳ _∨_
∧-distribʳ-∨ x y z = begin
  (y ∨ z) ∧ x    ≈⟨ ∧-comm _ _ ⟩
  x ∧ (y ∨ z)    ≈⟨ ∧-distribˡ-∨ _ _ _ ⟩
  x ∧ y ∨ x ∧ z  ≈⟨ ∧-comm _ _ ⟨ ∨-cong ⟩ ∧-comm _ _ ⟩
  y ∧ x ∨ z ∧ x  ∎

∧-distrib-∨ : _∧_ DistributesOver _∨_
∧-distrib-∨ = ∧-distribˡ-∨ , ∧-distribʳ-∨

-- The dual construction is also a distributive lattice.

∧-∨-isDistributiveLattice : IsDistributiveLattice _≈_ _∧_ _∨_
∧-∨-isDistributiveLattice = record
  { isLattice    = ∧-∨-isLattice
  ; ∨-distribʳ-∧ = ∧-distribʳ-∨
  }

∧-∨-distributiveLattice : DistributiveLattice _ _
∧-∨-distributiveLattice = record
  { isDistributiveLattice = ∧-∨-isDistributiveLattice
  }

-- One can replace the underlying equality with an equivalent one.

replace-equality : {_≈′_ : Rel Carrier dl₂} →
                   (∀ {x y} → x ≈ y ⇔ (x ≈′ y)) →
                   DistributiveLattice _ _
replace-equality {_≈′_} ≈⇔≈′ = record
  { _≈_                   = _≈′_
  ; _∧_                   = _∧_
  ; _∨_                   = _∨_
  ; isDistributiveLattice = record
    { isLattice    = Lattice.isLattice
                       (LatticeProperties.replace-equality lattice ≈⇔≈′)
    ; ∨-distribʳ-∧ = λ x y z → to ⟨$⟩ ∨-distribʳ-∧ x y z
    }
  } where open module E {x y} = Equivalence (≈⇔≈′ {x} {y})


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

∨-∧-distribˡ = ∨-distribˡ-∧
{-# WARNING_ON_USAGE ∨-∧-distribˡ
"Warning: ∨-∧-distribˡ was deprecated in v1.1.
Please use ∨-distribˡ-∧ instead."
#-}
∨-∧-distrib = ∨-distrib-∧
{-# WARNING_ON_USAGE ∨-∧-distrib
"Warning: ∨-∧-distrib was deprecated in v1.1.
Please use ∨-distrib-∧ instead."
#-}
∧-∨-distribˡ = ∧-distribˡ-∨
{-# WARNING_ON_USAGE ∧-∨-distribˡ
"Warning: ∧-∨-distribˡ was deprecated in v1.1.
Please use ∧-distribˡ-∨ instead."
#-}
∧-∨-distribʳ = ∧-distribʳ-∨
{-# WARNING_ON_USAGE ∧-∨-distribʳ
"Warning: ∧-∨-distribʳ was deprecated in v1.1.
Please use ∧-distribʳ-∨ instead."
#-}
∧-∨-distrib = ∧-distrib-∨
{-# WARNING_ON_USAGE ∧-∨-distrib
"Warning: ∧-∨-distrib was deprecated in v1.1.
Please use ∧-distrib-∨ instead."
#-}
