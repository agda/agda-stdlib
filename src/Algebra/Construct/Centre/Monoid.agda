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
open import Algebra.Morphism.MonoidMonomorphism using (isMonoid)
open import Function.Base using (id)

open import Algebra.Properties.Monoid monoid using (ε-central)

private
  module G = Monoid monoid


------------------------------------------------------------------------
-- Definition

-- Re-export the underlying sub-Semigroup

open import Algebra.Construct.Centre.Semigroup G.semigroup as Z public
  using (Center; ι; ∙-comm)

-- Now, can define a sub-Monoid

ε : Center
ε = record
  { ι = G.ε
  ; central = ε-central
  }

domain : RawMonoid _ _
domain = record { RawMagma Z.domain; ε = ε }

isMonoidHomomorphism : IsMonoidHomomorphism domain G.rawMonoid ι
isMonoidHomomorphism = record
  { isMagmaHomomorphism = Z.isMagmaHomomorphism
  ; ε-homo = G.refl
  }

isMonoidMonomorphism : IsMonoidMonomorphism domain G.rawMonoid ι
isMonoidMonomorphism = record
  { isMonoidHomomorphism = isMonoidHomomorphism
  ; injective = id
  }

-- And hence a CommutativeMonoid

commutativeMonoid : CommutativeMonoid _ _
commutativeMonoid = record
  { isCommutativeMonoid = record
    { isMonoid = isMonoid isMonoidMonomorphism G.isMonoid
    ; comm = ∙-comm
    }
  }

Z[_] = commutativeMonoid
