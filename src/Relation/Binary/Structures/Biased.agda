------------------------------------------------------------------------
-- The Agda standard library
--
-- Ways to give instances of certain structures where some fields can
-- be given in terms of others
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Relation.Binary`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core

module Relation.Binary.Structures.Biased
  {a ℓ} {A : Set a} -- The underlying set
  (_≈_ : Rel A ℓ)   -- The underlying equality relation
  where

open import Level using (Level; _⊔_)
open import Relation.Binary.Consequences
open import Relation.Binary.Definitions
open import Relation.Binary.Structures _≈_

private
  variable
    ℓ₂ : Level

-- To construct a StrictTotalOrder you only need to prove transitivity and
-- trichotomy as the current implementation of `Trichotomous` subsumes
-- irreflexivity and asymmetry.
record IsStrictTotalOrderᶜ (_<_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence
    trans         : Transitive _<_
    compare       : Trichotomous _≈_ _<_

  isStrictTotalOrderᶜ : IsStrictTotalOrder _<_
  isStrictTotalOrderᶜ = record
    { isStrictPartialOrder = record
      { isEquivalence = isEquivalence
      ; irrefl = tri⇒irr compare
      ; trans = trans
      ; <-resp-≈ = trans∧tri⇒resp Eq.sym Eq.trans trans compare
      }
    ; compare = compare
    } where module Eq = IsEquivalence isEquivalence

open IsStrictTotalOrderᶜ public
  using (isStrictTotalOrderᶜ)
