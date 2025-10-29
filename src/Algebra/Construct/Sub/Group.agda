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
    Sub : RawGroup c′ ℓ′

  private
    module Sub = RawGroup Sub

  field
    ι : Sub.Carrier → G.Carrier
    ι-monomorphism : IsGroupMonomorphism Sub G.rawGroup ι

  module ι = IsGroupMonomorphism ι-monomorphism

  isGroup : IsGroup Sub._≈_ Sub._∙_ Sub.ε Sub._⁻¹
  isGroup = GroupMonomorphism.isGroup ι-monomorphism G.isGroup

  group : Group _ _
  group = record { isGroup = isGroup }

  open Group group public hiding (isGroup)
