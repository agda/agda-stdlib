------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of subgroup via Group monomorphism
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group; RawGroup)

module Algebra.Construct.Sub.Group {c ℓ} (G : Group c ℓ) where

open import Algebra.Morphism.Structures using (IsGroupMonomorphism)
open import Algebra.Morphism.GroupMonomorphism using (isGroup)
open import Level using (suc; _⊔_)

private
  module G = Group G

record Subgroup c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field
    domain         : RawGroup c′ ℓ′
    ι              : _ → G.Carrier
    ι-monomorphism : IsGroupMonomorphism domain G.rawGroup ι

  module ι = IsGroupMonomorphism ι-monomorphism

  group : Group _ _
  group = record { isGroup = isGroup ι-monomorphism G.isGroup }

  open Group group public
