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

open import Algebra.Morphism.Structures using (IsMonoidMonomorphism)
open import Algebra.Morphism.MonoidMonomorphism using (isMonoid)
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

domain : RawMonoid _ _
domain = record { RawMagma Z.domain; ε = ε }
  where
  ε : Centre
  ε = record
    { ι = X.ε
    ; central = ε-central
    }

isMonoidMonomorphism : IsMonoidMonomorphism domain X.rawMonoid ι
isMonoidMonomorphism = record
  { isMonoidHomomorphism = record
    { isMagmaHomomorphism = Z.isMagmaHomomorphism
    ; ε-homo = X.refl
    }
  ; injective = id
  }

-- Public export of the sub-X-homomorphisms

open IsMonoidMonomorphism isMonoidMonomorphism public

-- And hence a CommutativeMonoid

commutativeMonoid : CommutativeMonoid _ _
commutativeMonoid = record
  { isCommutativeMonoid = record
    { isMonoid = isMonoid isMonoidMonomorphism X.isMonoid
    ; comm = ∙-comm
    }
  }

-- Public export of the sub-X-structures/bundles

open CommutativeMonoid commutativeMonoid public

-- Public export of the bundle

Z[_] = commutativeMonoid
