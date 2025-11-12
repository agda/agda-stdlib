------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of Z[ G ] the centre of a Monoid G
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles
  using (CommutativeMonoid; Monoid; RawMonoid; RawMagma)

module Algebra.Construct.Centre.Monoid {c ℓ} (G : Monoid c ℓ) where

open import Algebra.Morphism.Structures using (IsMonoidMonomorphism)
open import Function.Base using (id; _∘_)

import Algebra.Construct.Centre.Semigroup as Centre
open import Algebra.Construct.Sub.Monoid G using (Submonoid)

private
  module G = Monoid G
  module Z = Centre G.semigroup


------------------------------------------------------------------------
-- Definition

open Z public
  using (Center; ι; central; ∙-comm)
  hiding (module ι)

ε : Center
ε = record
  { ι = G.ε
  ; central = λ k → G.trans (G.identityˡ k) (G.sym (G.identityʳ k))
  }

domain : RawMonoid _ _
domain = record { RawMagma Z.domain ; ε = ε }

ι-isMonoidMonomorphism : IsMonoidMonomorphism domain _ _
ι-isMonoidMonomorphism = record
  { isMonoidHomomorphism = record
    { isMagmaHomomorphism = Z.ι.isMagmaHomomorphism
    ; ε-homo = G.refl
    }
  ; injective = id
  }

module ι = IsMonoidMonomorphism ι-isMonoidMonomorphism


------------------------------------------------------------------------
-- Public exports

monoid : Monoid _ _
monoid = Submonoid.monoid record { ι-monomorphism = ι-isMonoidMonomorphism }

commutativeMonoid : CommutativeMonoid _ _
commutativeMonoid = record
  { isCommutativeMonoid = record
    { isMonoid = isMonoid
    ; comm = ∙-comm
    }
  }
  where open Monoid monoid using (isMonoid)

Z[_] = commutativeMonoid

