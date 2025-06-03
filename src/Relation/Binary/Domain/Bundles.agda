------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for domain theory
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Domain.Bundles where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Domain.Structures
open import Relation.Binary.Domain.Definitions

private
  variable
    o ℓ e o' ℓ' e' ℓ₂ : Level
    Ix A B : Set o

------------------------------------------------------------------------
-- Directed Complete Partial Orders
------------------------------------------------------------------------

record DirectedFamily {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {B : Set c} (f : B → Poset.Carrier P) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isDirectedFamily : IsDirectedFamily P f
  
  open IsDirectedFamily isDirectedFamily public

record DirectedCompletePartialOrder (c ℓ₁ ℓ₂ : Level) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    poset                             : Poset c ℓ₁ ℓ₂
    isDirectedCompletePartialOrder    : IsDirectedCompletePartialOrder poset

  open Poset poset public
  open IsDirectedCompletePartialOrder isDirectedCompletePartialOrder public

------------------------------------------------------------------------
-- Scott-continuous functions
------------------------------------------------------------------------

record ScottContinuous {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {Q : Poset c ℓ₁ ℓ₂} :
  Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    f                 : Poset.Carrier P → Poset.Carrier Q
    isScottContinuous : IsScottContinuous {P = P} {Q = Q} f

------------------------------------------------------------------------
-- Lubs
------------------------------------------------------------------------

record Lub {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {B : Set c} (f : B → Poset.Carrier P) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  open Poset P
  field
    lub   : Carrier
    isLub : IsLub P f lub
