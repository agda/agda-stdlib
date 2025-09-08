------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by meet semilattices
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Lattice.Filter
  {κ ℓ₁ ℓ₂} (P : BoundedMeetSemilattice κ ℓ₁ ℓ₂) where

open import Function.Base using (flip; _∘_)
open import Relation.Binary.Structures using (IsDecPartialOrder)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.Filter using (IsFilter)
open import Data.Product.Base using (∃-syntax; _×_; _,_; proj₁; proj₂)

open BoundedMeetSemilattice P

open import Relation.Binary.Lattice.Properties.MeetSemilattice meetSemilattice

open import Relation.Binary.Properties.Poset poset using (≥-isPartialOrder)
import Relation.Binary.Lattice.Properties.JoinSemilattice as J

-- The dual construction is a join semilattice.

fact0 : (F : Carrier → Set κ) → IsFilter F _≤_ → F ⊤
fact0 F filter = 
  let (x ,  Fx) = downDirected .proj₁
  in upClosed x ⊤ (maximum x , Fx)
  where
    open IsFilter filter

fact1 : (F : Carrier → Set κ) → IsFilter F _≤_ → (∀ x y → F x × F y → F (x ∧ y))
fact1 F filter x y (Fx , Fy) = 
  let (z , Fz , z≤x , z≤y) = downDirected .proj₂ x y (Fx , Fy)
  in upClosed z (x ∧ y) (∧-greatest z≤x z≤y , Fz)
  where
    open IsFilter filter
