------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Boolean Rings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles
  using (CommutativeRing; BooleanSemiring; BooleanRing)

module Algebra.Properties.BooleanRing
  {c ℓ} (booleanRing : BooleanRing c ℓ) where

open import Function.Base using (_∘_)
open import Data.Product.Base using (_,_)

open BooleanRing booleanRing
open import Algebra.Structures _≈_
  using (IsBooleanSemiring)
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Re-export properties of Commutative Rings

open import Algebra.Properties.CommutativeRing commutativeRing public

------------------------------------------------------------------------
-- Structures

isBooleanSemiring : IsBooleanSemiring _+_ _*_ 0# 1#
isBooleanSemiring = record
  { isSemiring = isSemiring
  ; +-cancel = +-cancel
  ; *-idem = *-idem
  }

open IsBooleanSemiring isBooleanSemiring public
  using (*-isIdempotentMonoid)

------------------------------------------------------------------------
-- Bundles

booleanSemiring : BooleanSemiring _ _
booleanSemiring = record { isBooleanSemiring = isBooleanSemiring }

open BooleanSemiring booleanSemiring public
  using (*-idempotentMonoid)

------------------------------------------------------------------------
-- Export properties of Boolean semirings

open import Algebra.Properties.BooleanSemiring booleanSemiring public
  hiding (isBooleanRing; booleanRing)

------------------------------------------------------------------------
-- Further consequences

-x≈x : ∀ x → - x ≈ x
-x≈x = x+y≈0⇒y≈x ∘ -‿inverseʳ

