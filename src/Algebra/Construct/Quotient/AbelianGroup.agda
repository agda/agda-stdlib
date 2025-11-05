------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotient Abelian groups
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group; AbelianGroup)
import Algebra.Construct.Sub.AbelianGroup as AbelianSubgroup

module Algebra.Construct.Quotient.AbelianGroup
  {c ℓ} (G : AbelianGroup c ℓ)
  (open AbelianSubgroup G using (Subgroup; normalSubgroup)) 
  {c′ ℓ′} (N : Subgroup c′ ℓ′)
  where

private
  module G = AbelianGroup G

-- Re-export the quotient group

open import Algebra.Construct.Quotient.Group G.group (normalSubgroup N) public

-- With its additional bundle

quotientAbelianGroup : AbelianGroup c _
quotientAbelianGroup = record
  { isAbelianGroup = record
    { isGroup = isGroup
    ; comm = λ g h → ≈⇒≋ (G.comm g h)
    }
  } where open Group quotientGroup

-- Public re-exports, as needed?
