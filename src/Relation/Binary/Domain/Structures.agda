------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for domain theory
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Domain.Structures where

open import Data.Product using (_×_; _,_)
open import Data.Nat.Properties using (≤-trans)
open import Function using (_∘_)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Domain.Definitions
open import Relation.Binary.Morphism.Structures using (IsOrderHomomorphism)

private variable
  o ℓ e o' ℓ' e' ℓ₂ : Level
  Ix A B : Set o

module _ {c ℓ₁ ℓ₂ : Level} (P : Poset c ℓ₁ ℓ₂) where
  open Poset P

  record IsDirectedFamily {Ix : Set c} (s : Ix → Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    no-eta-equality
    field
      elt : Ix
      SemiDirected : IsSemidirectedFamily P s

  record IsLub {Ix : Set c} (s : Ix → Carrier) (lub : Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      is-upperbound : ∀ i → s i ≤ lub
      is-least : ∀ y → (∀ i → s i ≤ y) → lub ≤ y

  record IsDCPO : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      ⋁ : ∀ {Ix : Set c}
        → (s : Ix → Carrier)
        → IsDirectedFamily s
        → Carrier
      ⋁-isLub : ∀ {Ix : Set c}
        → (s : Ix → Carrier)
        → (dir : IsDirectedFamily s)
        → IsLub s (⋁ s dir)

    module _ {Ix : Set c} {s : Ix → Carrier} {dir : IsDirectedFamily s} where
      open IsLub (⋁-isLub s dir)
        renaming (is-upperbound to ⋁-≤; is-least to ⋁-least)
        public

module _ {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {Q : Poset c ℓ₁ ℓ₂} where

  private
    module P = Poset P
    module Q = Poset Q

  record IsScottContinuous (f : P.Carrier → Q.Carrier) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      PreserveLub : ∀ {Ix : Set c} {s : Ix → P.Carrier}
        → (dir : IsDirectedFamily P s)
        → (lub : P.Carrier)
        → IsLub P s lub
        → IsLub Q (f ∘ s) (f lub)
      PreserveEquality : ∀ {x y} → x P.≈ y → f x Q.≈ f y
