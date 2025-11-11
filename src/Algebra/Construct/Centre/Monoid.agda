------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre of a Group
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles
  using (CommutativeMonoid; Monoid; RawMonoid; RawMagma)

module Algebra.Construct.Centre.Monoid {c ℓ} (G : Monoid c ℓ) where

open import Algebra.Morphism.Structures using (IsMonoidHomomorphism)
open import Function.Base using (id; _∘_)

import Algebra.Construct.Centre.Semigroup as Centre
open import Algebra.Construct.Sub.Monoid G using (Submonoid)

private
  module G = Monoid G
  module Z = Centre G.semigroup


------------------------------------------------------------------------
-- Definition

open Z public
  using (Center; ι; central)

ε : Center
ε = record
  { ι = G.ε
  ; central = λ k → G.trans (G.identityˡ k) (G.sym (G.identityʳ k))
  }

domain : RawMonoid _ _
domain = record { RawMagma Z.domain ; ε = ε }

ι-isMonoidHomomorphism : IsMonoidHomomorphism domain _ _
ι-isMonoidHomomorphism = record
  { isMagmaHomomorphism = Z.ι-isMagmaHomomorphism
  ; ε-homo = G.refl
  }


------------------------------------------------------------------------
-- Public exports

monoid : Monoid _ _
monoid = Submonoid.monoid record
  { domain = domain
  ; ι = ι
  ; ι-monomorphism = record
    { isMonoidHomomorphism = ι-isMonoidHomomorphism
    ; injective = id
    }
  }

commutativeMonoid : CommutativeMonoid _ _
commutativeMonoid = record
  { isCommutativeMonoid = record
    { isMonoid = isMonoid
    ; comm = λ g → central g ∘ ι
    }
  }
  where open Monoid monoid using (isMonoid)

Z[_] = commutativeMonoid

