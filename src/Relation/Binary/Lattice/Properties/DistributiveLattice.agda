------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties for distributive lattice
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Lattice.Properties.DistributiveLattice
  {c ℓ₁ ℓ₂} (L : DistributiveLattice c ℓ₁ ℓ₂) where

open DistributiveLattice L hiding (refl)

open import Algebra.Definitions _≈_
open import Data.Product.Base using (_,_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Reasoning.Setoid setoid
open import Relation.Binary.Lattice.Properties.Lattice lattice
open import Relation.Binary.Lattice.Properties.MeetSemilattice meetSemilattice
open import Relation.Binary.Lattice.Properties.JoinSemilattice joinSemilattice

open Setoid setoid

∧-distribʳ-∨ : _∧_ DistributesOverʳ _∨_
∧-distribʳ-∨ x y z = begin
  (y ∨ z) ∧ x    ≈⟨ ∧-comm _ _ ⟩
  x ∧ (y ∨ z)    ≈⟨ ∧-distribˡ-∨ x y z ⟩
  x ∧ y ∨ x ∧ z  ≈⟨ ∨-cong (∧-comm _ _) (∧-comm _ _) ⟩
  y ∧ x ∨ z ∧ x  ∎

∧-distrib-∨ : _∧_ DistributesOver _∨_
∧-distrib-∨ = ∧-distribˡ-∨ , ∧-distribʳ-∨

∨-distribˡ-∧ : _∨_ DistributesOverˡ _∧_
∨-distribˡ-∧ x y z = begin
  x ∨ y ∧ z                  ≈⟨ ∨-cong (sym (∨-absorbs-∧ x y)) refl ⟩
  (x ∨ x ∧ y) ∨ y ∧ z        ≈⟨ ∨-cong (∨-cong refl (∧-comm _ _)) refl ⟩
  (x ∨ y ∧ x) ∨ y ∧ z        ≈⟨ ∨-assoc x (y ∧ x) (y ∧ z) ⟩
  x ∨ y ∧ x ∨ y ∧ z          ≈⟨ ∨-cong refl (sym (∧-distribˡ-∨ y x z)) ⟩
  x ∨ y ∧ (x ∨ z)            ≈⟨ ∨-cong (sym (∧-absorbs-∨ _ _)) refl ⟩
  x ∧ (x ∨ z) ∨ y ∧ (x ∨ z)  ≈⟨ sym (∧-distribʳ-∨ (x ∨ z) x y) ⟩
  (x ∨ y) ∧ (x ∨ z)          ∎

∨-distribʳ-∧ : _∨_ DistributesOverʳ _∧_
∨-distribʳ-∧ x y z = begin
  y ∧ z ∨ x          ≈⟨ ∨-comm _ _ ⟩
  x ∨ y ∧ z          ≈⟨ ∨-distribˡ-∧ _ _ _ ⟩
  (x ∨ y) ∧ (x ∨ z)  ≈⟨ ∧-cong (∨-comm _ _) (∨-comm _ _) ⟩
  (y ∨ x) ∧ (z ∨ x)  ∎

∨-distrib-∧ : _∨_ DistributesOver _∧_
∨-distrib-∧ = ∨-distribˡ-∧ , ∨-distribʳ-∧
