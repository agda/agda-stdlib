------------------------------------------------------------------------
-- The Agda standard library
--
-- The structure of a SuccessorSet
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

module Algebra.Structures.IsSuccessorSet
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Core using (Op₁)
open import Algebra.Definitions _≈_
open import Level using (_⊔_)

record IsSuccessorSet (suc# : Op₁ A) (zero# : A) : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_
    suc#-cong     : Congruent₁ suc#

  open IsEquivalence isEquivalence public

  setoid : Setoid a ℓ
  setoid = record { isEquivalence = isEquivalence }
