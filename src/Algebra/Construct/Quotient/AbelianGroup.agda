------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotient Abelian groups
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group; AbelianGroup)
import Algebra.Construct.Sub.AbelianGroup as AbelianSubgroup
import Algebra.Construct.Quotient.Group as Quotient

module Algebra.Construct.Quotient.AbelianGroup
  {c ℓ} (G : AbelianGroup c ℓ)
  (open AbelianSubgroup G using (Subgroup; normalSubgroup))
  {c′ ℓ′} (N : Subgroup c′ ℓ′)
  where

private
  module G = AbelianGroup G

-- Re-export the quotient group

open Quotient G.group (normalSubgroup N) public
  hiding (_/_)

-- With its additional bundle

abelianGroup : AbelianGroup c _
abelianGroup = record
  { isAbelianGroup = record
    { isGroup = isGroup
    ; comm = λ g h → ≈⇒≋ (G.comm g h)
    }
  } where open Group group

-- Public re-exports

_/_ = abelianGroup
