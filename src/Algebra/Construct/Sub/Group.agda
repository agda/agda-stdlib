------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of subgroups
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group; RawGroup)

module Algebra.Construct.Sub.Group {c ℓ} (G : Group c ℓ) where

private
  module G = Group G

open import Algebra.Structures using (IsGroup)
open import Algebra.Morphism.Structures using (IsGroupMonomorphism)
import Algebra.Morphism.GroupMonomorphism as GroupMonomorphism
open import Level using (suc; _⊔_)

record Subgroup c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field
    domain : RawGroup c′ ℓ′

  private
    module H = RawGroup domain

  field
    ι : H.Carrier → G.Carrier
    ι-monomorphism : IsGroupMonomorphism domain G.rawGroup ι

  module ι = IsGroupMonomorphism ι-monomorphism

  isGroup : IsGroup H._≈_ H._∙_ H.ε H._⁻¹
  isGroup = GroupMonomorphism.isGroup ι-monomorphism G.isGroup

  group : Group _ _
  group = record { isGroup = isGroup }

  open Group group public hiding (isGroup)
