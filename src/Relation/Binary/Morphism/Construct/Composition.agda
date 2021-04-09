------------------------------------------------------------------------
-- The Agda standard library
--
-- The composition of morphisms between binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Function.Base using (_∘_)
open import Function.Construct.Composition using (surjective)
open import Level using (Level)
open import Relation.Binary
open import Relation.Binary.Morphism.Bundles
open import Relation.Binary.Morphism.Structures

module Relation.Binary.Morphism.Construct.Composition where

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level
    A B C : Set a
    ≈₁ ≈₂ ≈₃ ∼₁ ∼₂ ∼₃ : Rel A ℓ₁
    f g : A → B

------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------
-- Structures

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
isRelIsomorphism {≈₁ = ≈₁} ≈₃-trans m₁ m₂ = record
  { isMonomorphism = isRelMonomorphism F.isMonomorphism G.isMonomorphism
  ; surjective     = surjective ≈₁ _ _ ≈₃-trans G.cong F.surjective G.surjective
  } where module F = IsRelIsomorphism m₁; module G = IsRelIsomorphism m₂

------------------------------------------------------------------------
-- Bundles

module _ {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} {U : Setoid c ℓ₃} where

  setoidHomomorphism : SetoidHomomorphism S T →
                       SetoidHomomorphism T U →
                       SetoidHomomorphism S U
  setoidHomomorphism ST TU = record
    { isRelHomomorphism = isRelHomomorphism ST.isRelHomomorphism TU.isRelHomomorphism
    } where module ST = SetoidHomomorphism ST; module TU = SetoidHomomorphism TU

  setoidMonomorphism : SetoidMonomorphism S T →
                       SetoidMonomorphism T U →
                       SetoidMonomorphism S U
  setoidMonomorphism ST TU = record
    { isRelMonomorphism = isRelMonomorphism ST.isRelMonomorphism TU.isRelMonomorphism
    } where module ST = SetoidMonomorphism ST; module TU = SetoidMonomorphism TU

  setoidIsomorphism : SetoidIsomorphism S T →
                      SetoidIsomorphism T U →
                      SetoidIsomorphism S U
  setoidIsomorphism ST TU = record
    { isRelIsomorphism = isRelIsomorphism (Setoid.trans U) ST.isRelIsomorphism TU.isRelIsomorphism
    } where module ST = SetoidIsomorphism ST; module TU = SetoidIsomorphism TU

------------------------------------------------------------------------
-- Orders
------------------------------------------------------------------------
-- Structures

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
isOrderIsomorphism {≈₁ = ≈₁} ≈₃-trans m₁ m₂ = record
  { isOrderMonomorphism = isOrderMonomorphism F.isOrderMonomorphism G.isOrderMonomorphism
  ; surjective          = surjective ≈₁ _ _ ≈₃-trans G.cong F.surjective G.surjective
  } where module F = IsOrderIsomorphism m₁; module G = IsOrderIsomorphism m₂

------------------------------------------------------------------------
-- Bundles

module _ {P : Preorder a ℓ₁ ℓ₂} {Q : Preorder b ℓ₃ ℓ₄} {R : Preorder c ℓ₅ ℓ₆} where

  preorderHomomorphism : PreorderHomomorphism P Q →
                         PreorderHomomorphism Q R →
                         PreorderHomomorphism P R
  preorderHomomorphism PQ QR = record
    { isOrderHomomorphism = isOrderHomomorphism PQ.isOrderHomomorphism QR.isOrderHomomorphism
    } where module PQ = PreorderHomomorphism PQ; module QR = PreorderHomomorphism QR

module _ {P : Poset a ℓ₁ ℓ₂} {Q : Poset b ℓ₃ ℓ₄} {R : Poset c ℓ₅ ℓ₆} where

  posetHomomorphism : PosetHomomorphism P Q →
                      PosetHomomorphism Q R →
                      PosetHomomorphism P R
  posetHomomorphism PQ QR = record
    { isOrderHomomorphism = isOrderHomomorphism PQ.isOrderHomomorphism QR.isOrderHomomorphism
    } where module PQ = PosetHomomorphism PQ; module QR = PosetHomomorphism QR
