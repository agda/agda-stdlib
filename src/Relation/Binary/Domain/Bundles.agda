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
-- DCPOs
------------------------------------------------------------------------

record DCPO (c ℓ₁ ℓ₂ : Level) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    poset   : Poset c ℓ₁ ℓ₂
    DcpoStr : IsDCPO poset

  open Poset poset public
  open IsDCPO DcpoStr public

------------------------------------------------------------------------
-- Scott-continuous functions
------------------------------------------------------------------------

record ScottContinuous {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {Q : Poset c ℓ₁ ℓ₂} :
  Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    f             : Poset.Carrier P → Poset.Carrier Q
    Scottfunction : IsScottContinuous {P = P} {Q = Q} f

------------------------------------------------------------------------
-- Lubs
------------------------------------------------------------------------

record Lub {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {Ix : Set c} (s : Ix → Poset.Carrier P) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  private
    module P = Poset P
  field
    lub           : P.Carrier
    is-upperbound : ∀ i → P._≤_ (s i) lub
    is-least      : ∀ y → (∀ i → P._≤_ (s i) y) → P._≤_ lub y
