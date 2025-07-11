------------------------------------------------------------------------
-- The Agda standard library
--
-- The `IsSemigroup` and related algebraic structures
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

module Algebra.Structures.IsSemigroup
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

-- The file is divided into sections depending on the arities of the
-- components of the algebraic structure.

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions _≈_
import Algebra.Consequences.Setoid as Consequences
open import Algebra.Structures.IsMagma _≈_
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Semigroups
------------------------------------------------------------------------

record IsSemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    assoc   : Associative ∙

  open IsMagma isMagma public


record IsBand (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    idem        : Idempotent ∙

  open IsSemigroup isSemigroup public


record IsCommutativeSemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    comm        : Commutative ∙

  open IsSemigroup isSemigroup public

  isCommutativeMagma : IsCommutativeMagma ∙
  isCommutativeMagma = record
    { isMagma = isMagma
    ; comm    = comm
    }


record IsCommutativeBand (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isBand : IsBand ∙
    comm   : Commutative ∙

  open IsBand isBand public

  isCommutativeSemigroup : IsCommutativeSemigroup ∙
  isCommutativeSemigroup = record { isSemigroup = isSemigroup ; comm = comm }

  open IsCommutativeSemigroup isCommutativeSemigroup public
    using (isCommutativeMagma)
