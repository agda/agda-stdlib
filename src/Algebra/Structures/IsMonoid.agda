------------------------------------------------------------------------
-- The Agda standard library
--
-- Some algebraic structures (not packed up with sets, operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

module Algebra.Structures.IsMonoid
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

-- The file is divided into sections depending on the arities of the
-- components of the algebraic structure.

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions _≈_
import Algebra.Consequences.Setoid as Consequences
import Algebra.Properties.IsSemigroup as Properties
open import Algebra.Structures.IsMagma _≈_
open import Algebra.Structures.IsSemigroup _≈_
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Monoids
------------------------------------------------------------------------

record IsMonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isSemigroup : IsSemigroup ∙
    identity    : Identity ε ∙

  open IsSemigroup isSemigroup public

  identityˡ : LeftIdentity ε ∙
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε ∙
  identityʳ = proj₂ identity

  isUnitalMagma : IsUnitalMagma ∙ ε
  isUnitalMagma = record
    { isMagma  = isMagma
    ; identity = identity
    }


record IsCommutativeMonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isMonoid : IsMonoid ∙ ε
    comm     : Commutative ∙

  open IsMonoid isMonoid public
  open Properties isSemigroup public
    using (isAlternativeMagma; isFlexibleMagma)

  isCommutativeSemigroup : IsCommutativeSemigroup ∙
  isCommutativeSemigroup = record
    { isSemigroup = isSemigroup
    ; comm        = comm
    }

  open IsCommutativeSemigroup isCommutativeSemigroup public
    using (isCommutativeMagma)


record IsIdempotentMonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isMonoid : IsMonoid ∙ ε
    idem     : Idempotent ∙

  open IsMonoid isMonoid public
  open Properties isSemigroup public
    using (isAlternativeMagma; isFlexibleMagma)

  isBand : IsBand ∙
  isBand = record { isSemigroup = isSemigroup ; idem = idem }


record IsIdempotentCommutativeMonoid (∙ : Op₂ A)
                                     (ε : A) : Set (a ⊔ ℓ) where
  field
    isCommutativeMonoid : IsCommutativeMonoid ∙ ε
    idem                : Idempotent ∙

  open IsCommutativeMonoid isCommutativeMonoid public

  isIdempotentMonoid : IsIdempotentMonoid ∙ ε
  isIdempotentMonoid = record { isMonoid = isMonoid ; idem = idem }

  open IsIdempotentMonoid isIdempotentMonoid public
    using (isBand)

  isCommutativeBand : IsCommutativeBand ∙
  isCommutativeBand = record { isBand = isBand ; comm = comm }
