------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for domain theory
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Domain.Structures where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Domain.Definitions
  using (semidirected; leastupperbound; preserveLubs)
open import Relation.Binary.Morphism.Structures using (IsOrderHomomorphism)

private variable
  a b c c₁ c₂ ℓ ℓ₁ ℓ₂ ℓ₁₁ ℓ₁₂ ℓ₂₁ ℓ₂₂ : Level
  A B : Set a


module _ (P : Poset c ℓ₁ ℓ₂) where
  open Poset P

  record IsLub {b : Level} {B : Set b} (f : B → Carrier)
               (lub : Carrier) : Set (b ⊔ c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLeastUpperBound : leastupperbound _≤_ f lub

    isUpperBound : ∀ i → f i ≤ lub
    isUpperBound = proj₁ isLeastUpperBound

    isLeast : ∀ y → (∀ i → f i ≤ y) → lub ≤ y
    isLeast = proj₂ isLeastUpperBound

  record IsDirectedFamily {b : Level} {B : Set b} (f : B → Carrier) :
                          Set (b ⊔ c ⊔ ℓ₁ ⊔ ℓ₂) where
    no-eta-equality
    field
      elt            : B
      isSemidirected : semidirected _≤_ B f

  record IsDirectedCompletePartialOrder : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      ⋁ : ∀ {B : Set c} →
        (f : B → Carrier) →
        IsDirectedFamily f →
        Carrier
      ⋁-isLub : ∀ {B : Set c}
        → (f : B → Carrier)
        → (dir : IsDirectedFamily f)
        → IsLub f (⋁ f dir)

    module _ {B : Set c} {f : B → Carrier} {dir : IsDirectedFamily f} where
      open IsLub (⋁-isLub f dir)
        renaming (isUpperBound to ⋁-≤; isLeast to ⋁-least)
        public

------------------------------------------------------------------------
-- Scott‐continuous maps between two (possibly different‐universe) posets
------------------------------------------------------------------------

module _ (P : Poset c₁ ℓ₁₁ ℓ₁₂) (Q : Poset c₂ ℓ₂₁ ℓ₂₂)
  where
    module P = Poset P
    module Q = Poset Q

    record IsScottContinuous (f : P.Carrier → Q.Carrier) : Set (suc (c₁ ⊔ ℓ₁₁ ⊔ ℓ₁₂ ⊔ c₂ ⊔ ℓ₂₁ ⊔ ℓ₂₂))
      where
      field
        preservelub : preserveLubs P._≤_ Q._≤_ f
        isOrderHomomorphism : IsOrderHomomorphism P._≈_ Q._≈_ P._≤_ Q._≤_ f

      open IsOrderHomomorphism isOrderHomomorphism public
