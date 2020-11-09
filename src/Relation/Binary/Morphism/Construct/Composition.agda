------------------------------------------------------------------------
-- The Agda standard library
--
-- The composition of morphisms between binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Product using (_,_)
open import Function.Base using (id; _∘_)
open import Function.Definitions using (Congruent)
open import Function.Construct.Composition using (surjective)
open import Relation.Binary
open import Relation.Binary.Morphism.Structures

module Relation.Binary.Morphism.Construct.Composition
  {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c}
  {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {≈₃ : Rel C ℓ₃}
  {f : A → B} {g : B → C} where

------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

isRelHomomorphism : IsRelHomomorphism ≈₁ ≈₂ f →
                    IsRelHomomorphism ≈₂ ≈₃ g →
                    IsRelHomomorphism ≈₁ ≈₃ (g ∘ f)
isRelHomomorphism m₁ m₂ = record
  { cong = G.cong ∘ F.cong
  } where module F = IsRelHomomorphism m₁; module G = IsRelHomomorphism m₂

isRelMonomorphism : IsRelMonomorphism ≈₁ ≈₂ f →
                    IsRelMonomorphism ≈₂ ≈₃ g →
                    IsRelMonomorphism ≈₁ ≈₃ (g ∘ f)
isRelMonomorphism m₁ m₂ = record
  { isHomomorphism = isRelHomomorphism F.isHomomorphism G.isHomomorphism
  ; injective      = F.injective ∘ G.injective
  } where module F = IsRelMonomorphism m₁; module G = IsRelMonomorphism m₂

isRelIsomorphism : Transitive ≈₃ →
                   IsRelIsomorphism ≈₁ ≈₂ f →
                   IsRelIsomorphism ≈₂ ≈₃ g →
                   IsRelIsomorphism ≈₁ ≈₃ (g ∘ f)
isRelIsomorphism ≈₃-trans m₁ m₂ = record
  { isMonomorphism = isRelMonomorphism F.isMonomorphism G.isMonomorphism
  ; surjective     = surjective ≈₁ ≈₂ ≈₃ ≈₃-trans G.cong F.surjective G.surjective
  } where module F = IsRelIsomorphism m₁; module G = IsRelIsomorphism m₂

------------------------------------------------------------------------
-- Orders
------------------------------------------------------------------------

module _ {ℓ₄ ℓ₅ ℓ₆} {∼₁ : Rel A ℓ₄} {∼₂ : Rel B ℓ₅} {∼₃ : Rel C ℓ₆} where

  isOrderHomomorphism : IsOrderHomomorphism ≈₁ ≈₂ ∼₁ ∼₂ f →
                        IsOrderHomomorphism ≈₂ ≈₃ ∼₂ ∼₃ g →
                        IsOrderHomomorphism ≈₁ ≈₃ ∼₁ ∼₃ (g ∘ f)
  isOrderHomomorphism m₁ m₂ = record
    { cong = G.cong ∘ F.cong
    ; mono = G.mono ∘ F.mono
    } where module F = IsOrderHomomorphism m₁; module G = IsOrderHomomorphism m₂

  isOrderMonomorphism : IsOrderMonomorphism ≈₁ ≈₂ ∼₁ ∼₂ f →
                        IsOrderMonomorphism ≈₂ ≈₃ ∼₂ ∼₃ g →
                        IsOrderMonomorphism ≈₁ ≈₃ ∼₁ ∼₃ (g ∘ f)
  isOrderMonomorphism m₁ m₂ = record
    { isOrderHomomorphism = isOrderHomomorphism F.isOrderHomomorphism G.isOrderHomomorphism
    ; injective           = F.injective ∘ G.injective
    ; cancel              = F.cancel ∘ G.cancel
    } where module F = IsOrderMonomorphism m₁; module G = IsOrderMonomorphism m₂

  isOrderIsomorphism : Transitive ≈₃ →
                       IsOrderIsomorphism ≈₁ ≈₂ ∼₁ ∼₂ f →
                       IsOrderIsomorphism ≈₂ ≈₃ ∼₂ ∼₃ g →
                       IsOrderIsomorphism ≈₁ ≈₃ ∼₁ ∼₃ (g ∘ f)
  isOrderIsomorphism ≈₃-trans m₁ m₂ = record
    { isOrderMonomorphism = isOrderMonomorphism F.isOrderMonomorphism G.isOrderMonomorphism
    ; surjective          = surjective ≈₁ ≈₂ ≈₃ ≈₃-trans G.cong F.surjective G.surjective
    } where module F = IsOrderIsomorphism m₁; module G = IsOrderIsomorphism m₂
