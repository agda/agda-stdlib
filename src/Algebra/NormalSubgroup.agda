------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of normal subgroups
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group)

module Algebra.NormalSubgroup {c ℓ} (G : Group c ℓ)  where

open import Algebra.Construct.Sub.Group G using (Subgroup)
open import Data.Product.Base using (∃-syntax)
open import Level using (suc; _⊔_)

private
  module G = Group G

record NormalSubgroup c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field
    subgroup : Subgroup c′ ℓ′

  open Subgroup subgroup public

  field
    -- every element of N commutes in G
    normal : ∀ n g → ∃[ n′ ] g G.∙ ι n G.≈ ι n′ G.∙ g
