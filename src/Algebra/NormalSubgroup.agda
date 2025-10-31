------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of normal subgroups
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group)

module Algebra.NormalSubgroup {c ℓ} (G : Group c ℓ)  where

open import Algebra.Definitions
open import Algebra.Construct.Sub.Group G using (Subgroup)
open import Data.Product.Base using (∃-syntax; _,_)
open import Level using (suc; _⊔_)

private
  module G = Group G

-- every element of the subgroup commutes in G
Normal : ∀ {c′ ℓ′} → Subgroup c′ ℓ′ → Set (c ⊔ ℓ ⊔ c′)
Normal subgroup = ∀ n g → ∃[ n′ ] g G.∙ ι n G.≈ ι n′ G.∙ g
  where open Subgroup subgroup

record NormalSubgroup c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field
    subgroup : Subgroup c′ ℓ′
    normal : Normal subgroup

  open Subgroup subgroup public

abelian⇒subgroup-normal : ∀ {c′ ℓ′} → Commutative G._≈_ G._∙_ → (subgroup : Subgroup c′ ℓ′) → Normal subgroup
abelian⇒subgroup-normal ∙-comm subgroup n g = n , ∙-comm g (ι n)
  where open Subgroup subgroup
