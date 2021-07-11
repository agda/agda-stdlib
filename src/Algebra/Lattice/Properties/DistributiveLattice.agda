------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated names
{-# OPTIONS --warn=noUserWarning #-}

open import Algebra.Lattice.Bundles
import Algebra.Properties.Lattice as LatticeProperties
open import Relation.Binary
open import Function.Base
open import Data.Product using (_,_)

module Algebra.Lattice.Properties.DistributiveLattice
  {dl₁ dl₂} (DL : DistributiveLattice dl₁ dl₂)
  where

open DistributiveLattice DL
open import Algebra.Structures _≈_
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid

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
