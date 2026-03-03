------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre of an Monoid
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles
  using (Monoid; CommutativeMonoid; RawMagma; RawMonoid)

module Algebra.Construct.Centre.Monoid
  {c ℓ} (monoid : Monoid c ℓ)
  where

open import Algebra.Morphism.Structures
import Algebra.Morphism.MonoidMonomorphism as MonoidMonomorphism
  using (isMonoid)
open import Algebra.Structures using (IsMonoid; IsCommutativeMonoid)
open import Function.Base using (id)

open import Algebra.Properties.Monoid monoid using (ε-central)

private
  module X = Monoid monoid


------------------------------------------------------------------------
-- Definition

-- Re-export the underlying sub-Semigroup

open import Algebra.Construct.Centre.Semigroup X.semigroup as Z public
  using (Centre; ι; ∙-comm)

-- Now, can define a sub-Monoid

ε : Centre
ε = record
  { ι = X.ε
  ; central = ε-central
  }

domain : RawMonoid _ _
domain = record { RawMagma Z.domain; ε = ε }

isMonoidHomomorphism : IsMonoidHomomorphism domain X.rawMonoid ι
isMonoidHomomorphism = record
  { isMagmaHomomorphism = Z.isMagmaHomomorphism
  ; ε-homo = X.refl
  }

isMonoidMonomorphism : IsMonoidMonomorphism domain X.rawMonoid ι
isMonoidMonomorphism = record
  { isMonoidHomomorphism = isMonoidHomomorphism
  ; injective = id
  }

-- And hence a CommutativeMonoid

isMonoid : IsMonoid _ _ _
isMonoid = MonoidMonomorphism.isMonoid isMonoidMonomorphism X.isMonoid

isCommutativeMonoid : IsCommutativeMonoid _ _ _
isCommutativeMonoid = record
  { isMonoid = isMonoid
  ; comm = ∙-comm
  }

commutativeMonoid : CommutativeMonoid _ _
commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

Z[_] = commutativeMonoid
