------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties for distributive lattice
------------------------------------------------------------------------

open import Relation.Binary.Lattice

module Relation.Binary.Properties.DistributiveLattice
  {c ℓ₁ ℓ₂} (L : DistributiveLattice c ℓ₁ ℓ₂) where

open DistributiveLattice L hiding (refl)

open import Relation.Binary
open import Relation.Binary.SetoidReasoning
open import Algebra.FunctionProperties _≈_
open import Relation.Binary.Properties.MeetSemilattice meetSemilattice
open import Relation.Binary.Properties.JoinSemilattice joinSemilattice
open import Relation.Binary.Properties.Lattice lattice

open import Data.Product

private
  ≈-setoid : Setoid _ _
  ≈-setoid = record { isEquivalence = isEquivalence }

open Setoid ≈-setoid

∧-distribʳ-∨ : _∧_ DistributesOverʳ _∨_
∧-distribʳ-∨ x y z = begin⟨ ≈-setoid ⟩
                       (y ∨ z) ∧ x   ≈⟨ ∧-comm _ _ ⟩
                       x ∧ (y ∨ z)   ≈⟨ ∧-distribˡ-∨ x y z ⟩
                       x ∧ y ∨ x ∧ z ≈⟨ ∨-cong (∧-comm _ _) (∧-comm _ _) ⟩
                       y ∧ x ∨ z ∧ x ∎

∧-distrib-∨ : _∧_ DistributesOver _∨_
∧-distrib-∨ = ∧-distribˡ-∨ , ∧-distribʳ-∨

∨-distribˡ-∧ : _∨_ DistributesOverˡ _∧_
∨-distribˡ-∧ x y z = begin⟨ ≈-setoid ⟩
                       x ∨ y ∧ z                 ≈⟨ ∨-cong (sym (∨-absorbs-∧ x y)) refl ⟩
                       (x ∨ x ∧ y) ∨ y ∧ z       ≈⟨ ∨-cong (∨-cong refl (∧-comm _ _)) refl ⟩
                       (x ∨ y ∧ x) ∨ y ∧ z       ≈⟨ ∨-assoc x (y ∧ x) (y ∧ z) ⟩
                       x ∨ y ∧ x ∨ y ∧ z         ≈⟨ ∨-cong refl (sym (∧-distribˡ-∨ y x z)) ⟩
                       x ∨ y ∧ (x ∨ z)           ≈⟨ ∨-cong (sym (∧-absorbs-∨ _ _)) refl ⟩
                       x ∧ (x ∨ z) ∨ y ∧ (x ∨ z) ≈⟨ sym (∧-distribʳ-∨ (x ∨ z) x y) ⟩
                       (x ∨ y) ∧ (x ∨ z)         ∎

∨-distribʳ-∧ : _∨_ DistributesOverʳ _∧_
∨-distribʳ-∧ x y z = begin⟨ ≈-setoid ⟩
                       y ∧ z ∨ x         ≈⟨ ∨-comm _ _ ⟩
                       x ∨ y ∧ z         ≈⟨ ∨-distribˡ-∧ _ _ _ ⟩
                       (x ∨ y) ∧ (x ∨ z) ≈⟨ ∧-cong (∨-comm _ _) (∨-comm _ _) ⟩
                       (y ∨ x) ∧ (z ∨ x) ∎

∨-distrib-∧ : _∨_ DistributesOver _∧_
∨-distrib-∧ = ∨-distribˡ-∧ , ∨-distribʳ-∧
