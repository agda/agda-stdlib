------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded lattice
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Lattice.Properties.BoundedLattice
  {c ℓ₁ ℓ₂} (L : BoundedLattice c ℓ₁ ℓ₂) where

open BoundedLattice L

open import Algebra.Definitions _≈_
open import Data.Product.Base using (_,_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Lattice.Properties.MeetSemilattice meetSemilattice
open import Relation.Binary.Lattice.Properties.JoinSemilattice joinSemilattice

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
