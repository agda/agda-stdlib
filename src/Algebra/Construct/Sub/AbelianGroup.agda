------------------------------------------------------------------------
-- The Agda standard library
--
-- Subgroups of Abelian groups: necessarily Normal
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (AbelianGroup)

module Algebra.Construct.Sub.AbelianGroup {c ℓ} (G : AbelianGroup c ℓ) where

open import Algebra.Morphism.GroupMonomorphism using (isAbelianGroup)

private
  module G = AbelianGroup G

open import Algebra.Construct.Sub.Group.Normal G.group
  using (IsNormal; NormalSubgroup)

-- Re-export the notion of subgroup of the underlying Group

open import Algebra.Construct.Sub.Group G.group public
  using (Subgroup)

-- Then, for any such Subgroup:
-- * it defines an AbelianGroup
-- * and is, in fact, Normal

module _ {c′ ℓ′} (subgroup : Subgroup c′ ℓ′) where

  open Subgroup subgroup public
    using (ι; ι-monomorphism)

  abelianGroup : AbelianGroup c′ ℓ′
  abelianGroup = record
    { isAbelianGroup = isAbelianGroup ι-monomorphism G.isAbelianGroup }

  open AbelianGroup abelianGroup public

  isNormal : IsNormal subgroup
  isNormal = record { normal = λ n → G.comm (ι n) }

  normalSubgroup : NormalSubgroup c′ ℓ′
  normalSubgroup = record { isNormal = isNormal }

  open NormalSubgroup normalSubgroup public
    using (conjugate; normal)
