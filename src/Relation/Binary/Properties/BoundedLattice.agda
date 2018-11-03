------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded lattice
------------------------------------------------------------------------

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedLattice
  {c ℓ₁ ℓ₂} (L : BoundedLattice c ℓ₁ ℓ₂) where

open BoundedLattice L

open import Algebra.FunctionProperties _≈_
open import Data.Product using (_,_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.Properties.MeetSemilattice meetSemilattice
open import Relation.Binary.Properties.JoinSemilattice joinSemilattice

open Setoid setoid renaming (trans to ≈-trans)

∧-zeroʳ : RightZero ⊥ _∧_
∧-zeroʳ x = y≤x⇒x∧y≈y (minimum x)

∧-zeroˡ : LeftZero ⊥ _∧_
∧-zeroˡ x = ≈-trans (∧-comm ⊥ x) (∧-zeroʳ x)

∧-zero : Zero ⊥ _∧_
∧-zero = ∧-zeroˡ , ∧-zeroʳ

∨-zeroʳ : RightZero ⊤ _∨_
∨-zeroʳ x = x≤y⇒x∨y≈y (maximum x)

∨-zeroˡ : LeftZero ⊤ _∨_
∨-zeroˡ x = ≈-trans (∨-comm ⊤ x) (∨-zeroʳ x)

∨-zero : Zero ⊤ _∨_
∨-zero = ∨-zeroˡ , ∨-zeroʳ
