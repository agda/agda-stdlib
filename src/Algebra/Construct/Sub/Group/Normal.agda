------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of normal subgroups
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group)

module Algebra.Construct.Sub.Group.Normal {c ℓ} (G : Group c ℓ) where

open import Algebra.Construct.Sub.Group G using (Subgroup)
open import Level using (suc; _⊔_)

private
  module G = Group G

-- every element of the subgroup commutes in G
record IsNormal {c′ ℓ′} (subgroup : Subgroup c′ ℓ′) : Set (c ⊔ ℓ ⊔ c′) where
  open Subgroup subgroup using (ι)
  field
    conjugate : ∀ n g → _
    normal : ∀ n g → ι (conjugate n g) G.∙ g G.≈ g G.∙ ι n

record NormalSubgroup c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field
    subgroup : Subgroup c′ ℓ′
    isNormal : IsNormal subgroup

  open Subgroup subgroup public
  open IsNormal isNormal public
