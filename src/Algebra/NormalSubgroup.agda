------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of normal subgroups
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group; RawGroup)

module Algebra.NormalSubgroup {c ℓ} (G : Group c ℓ)  where

open Group G

open import Algebra.Structures using (IsGroup)
open import Algebra.Morphism.Structures
import Algebra.Morphism.GroupMonomorphism as GM
open import Data.Product.Base
open import Level using (suc; _⊔_)

record NormalSubgroup c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field
    -- N is a subgroup of G
    N : RawGroup c′ ℓ′
    ι : RawGroup.Carrier N → Carrier
    ι-monomorphism : IsGroupMonomorphism N rawGroup ι
    -- every element of N commutes in G
    normal : ∀ n g → ∃[ n′ ] g ∙ ι n ≈ ι n′ ∙ g

  module N = RawGroup N
  module ι = IsGroupMonomorphism ι-monomorphism

  N-isGroup : IsGroup N._≈_ N._∙_ N.ε N._⁻¹
  N-isGroup = GM.isGroup ι-monomorphism isGroup
