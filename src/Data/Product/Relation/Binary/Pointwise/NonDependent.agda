------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise products of binary relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Relation.Binary.Pointwise.NonDependent where

open import Data.Product.Base as Prod
open import Data.Product.Properties using (≡-dec)
open import Data.Sum.Base
open import Data.Unit.Base using (⊤)
open import Level using (Level; _⊔_; 0ℓ)
open import Function
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as P

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B : Set a
    R S ≈₁ ≈₂ : Rel A ℓ₁

------------------------------------------------------------------------
-- Definition

Pointwise : Rel A ℓ₁ → Rel B ℓ₂ → Rel (A × B) (ℓ₁ ⊔ ℓ₂)
Pointwise R S = (R on proj₁) -×- (S on proj₂)

------------------------------------------------------------------------
-- Pointwise preserves many relational properties

×-reflexive : ≈₁ ⇒ R → ≈₂ ⇒ S → Pointwise ≈₁ ≈₂ ⇒ Pointwise R S
×-reflexive refl₁ refl₂ = Prod.map refl₁ refl₂

×-refl : Reflexive R → Reflexive S → Reflexive (Pointwise R S)
×-refl refl₁ refl₂ = refl₁ , refl₂

×-irreflexive₁ : Irreflexive ≈₁ R →
                 Irreflexive (Pointwise ≈₁ ≈₂) (Pointwise R S)
×-irreflexive₁ ir x≈y x<y = ir (proj₁ x≈y) (proj₁ x<y)

×-irreflexive₂ : Irreflexive ≈₂ S →
                 Irreflexive (Pointwise ≈₁ ≈₂) (Pointwise R S)
×-irreflexive₂ ir x≈y x<y = ir (proj₂ x≈y) (proj₂ x<y)

×-symmetric : Symmetric R → Symmetric S → Symmetric (Pointwise R S)
×-symmetric sym₁ sym₂ = Prod.map sym₁ sym₂

×-transitive : Transitive R → Transitive S → Transitive (Pointwise R S)
×-transitive trans₁ trans₂ = Prod.zip trans₁ trans₂

×-antisymmetric : Antisymmetric ≈₁ R → Antisymmetric ≈₂ S →
                  Antisymmetric (Pointwise ≈₁ ≈₂) (Pointwise R S)
×-antisymmetric antisym₁ antisym₂ = Prod.zip antisym₁ antisym₂

×-asymmetric₁ : Asymmetric R → Asymmetric (Pointwise R S)
×-asymmetric₁ asym₁ x<y y<x = asym₁ (proj₁ x<y) (proj₁ y<x)

×-asymmetric₂ : Asymmetric S → Asymmetric (Pointwise R S)
×-asymmetric₂ asym₂ x<y y<x = asym₂ (proj₂ x<y) (proj₂ y<x)

×-respectsʳ : R Respectsʳ ≈₁ → S Respectsʳ ≈₂ →
             (Pointwise R S) Respectsʳ (Pointwise ≈₁ ≈₂)
×-respectsʳ resp₁ resp₂ = Prod.zip resp₁ resp₂

×-respectsˡ : R Respectsˡ ≈₁ → S Respectsˡ ≈₂ →
             (Pointwise R S) Respectsˡ (Pointwise ≈₁ ≈₂)
×-respectsˡ resp₁ resp₂ = Prod.zip resp₁ resp₂

×-respects₂ : R Respects₂ ≈₁ → S Respects₂ ≈₂ →
              (Pointwise R S) Respects₂ (Pointwise ≈₁ ≈₂)
×-respects₂ = Prod.zip ×-respectsʳ ×-respectsˡ

×-total : Symmetric R → Total R → Total S → Total (Pointwise R S)
×-total sym₁ total₁ total₂ (x₁ , x₂) (y₁ , y₂)
  with total₁ x₁ y₁ | total₂ x₂ y₂
... | inj₁ x₁∼y₁ | inj₁ x₂∼y₂ = inj₁ (     x₁∼y₁ , x₂∼y₂)
... | inj₁ x₁∼y₁ | inj₂ y₂∼x₂ = inj₂ (sym₁ x₁∼y₁ , y₂∼x₂)
... | inj₂ y₁∼x₁ | inj₂ y₂∼x₂ = inj₂ (     y₁∼x₁ , y₂∼x₂)
... | inj₂ y₁∼x₁ | inj₁ x₂∼y₂ = inj₁ (sym₁ y₁∼x₁ , x₂∼y₂)

×-decidable : Decidable R → Decidable S → Decidable (Pointwise R S)
×-decidable _≟₁_ _≟₂_ (x₁ , x₂) (y₁ , y₂) = (x₁ ≟₁ y₁) ×-dec (x₂ ≟₂ y₂)

------------------------------------------------------------------------
-- Structures can also be combined.

-- Some collections of properties which are preserved by ×-Rel.

×-isEquivalence : IsEquivalence R → IsEquivalence S →
                  IsEquivalence (Pointwise R S)
×-isEquivalence {R = R} {S = S} eq₁ eq₂ = record
  { refl  = ×-refl {R = R} {S = S} (refl eq₁) (refl eq₂)
  ; sym   = ×-symmetric {R = R} {S = S} (sym eq₁) (sym eq₂)
  ; trans = ×-transitive {R = R} {S = S} (trans eq₁) (trans eq₂)
  } where open IsEquivalence

×-isDecEquivalence : IsDecEquivalence R → IsDecEquivalence S →
                     IsDecEquivalence (Pointwise R S)
×-isDecEquivalence eq₁ eq₂ = record
  { isEquivalence = ×-isEquivalence
                      (isEquivalence eq₁) (isEquivalence eq₂)
  ; _≟_           = ×-decidable (_≟_ eq₁) (_≟_ eq₂)
  } where open IsDecEquivalence

×-isPreorder : IsPreorder ≈₁ R → IsPreorder ≈₂ S →
               IsPreorder (Pointwise ≈₁ ≈₂) (Pointwise R S)
×-isPreorder {R = R} {S = S} pre₁ pre₂ = record
  { isEquivalence = ×-isEquivalence
                      (isEquivalence pre₁) (isEquivalence pre₂)
  ; reflexive     = ×-reflexive {R = R} {S = S}
                      (reflexive pre₁) (reflexive pre₂)
  ; trans         = ×-transitive {R = R} {S = S}
                      (trans pre₁) (trans pre₂)
  } where open IsPreorder

×-isPartialOrder : IsPartialOrder ≈₁ R → IsPartialOrder ≈₂ S →
                   IsPartialOrder (Pointwise ≈₁ ≈₂) (Pointwise R S)
×-isPartialOrder {R = R} {S = S} po₁ po₂ = record
  { isPreorder = ×-isPreorder (isPreorder po₁) (isPreorder po₂)
  ; antisym    = ×-antisymmetric {R = R} {S = S}
                   (antisym po₁) (antisym po₂)
  } where open IsPartialOrder

×-isStrictPartialOrder : IsStrictPartialOrder ≈₁ R →
                         IsStrictPartialOrder ≈₂ S →
                         IsStrictPartialOrder (Pointwise ≈₁ ≈₂) (Pointwise R S)
×-isStrictPartialOrder {R = R} {≈₂ = ≈₂} {S = S} spo₁ spo₂ = record
  { isEquivalence = ×-isEquivalence
                      (isEquivalence spo₁) (isEquivalence spo₂)
  ; irrefl        = ×-irreflexive₁ {R = R} {≈₂ = ≈₂} {S = S}
                      (irrefl spo₁)
  ; trans         = ×-transitive {R = R} {S = S}
                      (trans spo₁) (trans spo₂)
  ; <-resp-≈      = ×-respects₂ (<-resp-≈ spo₁) (<-resp-≈ spo₂)
  } where open IsStrictPartialOrder

------------------------------------------------------------------------
-- Bundles

×-setoid : Setoid a ℓ₁ → Setoid b ℓ₂ → Setoid _ _
×-setoid s₁ s₂ = record
  { isEquivalence =
      ×-isEquivalence (isEquivalence s₁) (isEquivalence s₂)
  } where open Setoid

×-decSetoid : DecSetoid a ℓ₁ → DecSetoid b ℓ₂ → DecSetoid _ _
×-decSetoid s₁ s₂ = record
  { isDecEquivalence =
      ×-isDecEquivalence (isDecEquivalence s₁) (isDecEquivalence s₂)
  } where open DecSetoid

×-preorder : Preorder a ℓ₁ ℓ₂ → Preorder b ℓ₃ ℓ₄ → Preorder _ _ _
×-preorder p₁ p₂ = record
  { isPreorder = ×-isPreorder (isPreorder p₁) (isPreorder p₂)
  } where open Preorder

×-poset : Poset a ℓ₁ ℓ₂ → Poset b ℓ₃ ℓ₄ → Poset _ _ _
×-poset s₁ s₂ = record
  { isPartialOrder = ×-isPartialOrder (isPartialOrder s₁)
                     (isPartialOrder s₂)
  } where open Poset

×-strictPartialOrder : StrictPartialOrder a ℓ₁ ℓ₂ →
                       StrictPartialOrder b ℓ₃ ℓ₄ →
                       StrictPartialOrder _ _ _
×-strictPartialOrder s₁ s₂ = record
  { isStrictPartialOrder = ×-isStrictPartialOrder
                             (isStrictPartialOrder s₁)
                             (isStrictPartialOrder s₂)
  } where open StrictPartialOrder

------------------------------------------------------------------------
-- Additional notation

-- Infix combining setoids
infix 4 _×ₛ_
_×ₛ_ : Setoid a ℓ₁ → Setoid b ℓ₂ → Setoid _ _
_×ₛ_ = ×-setoid

------------------------------------------------------------------------
-- The propositional equality setoid over products can be
-- decomposed using ×-Rel

≡×≡⇒≡ : Pointwise _≡_ _≡_ ⇒ _≡_ {A = A × B}
≡×≡⇒≡ (P.refl , P.refl) = P.refl

≡⇒≡×≡ : _≡_ {A = A × B} ⇒ Pointwise _≡_ _≡_
≡⇒≡×≡ P.refl = (P.refl , P.refl)

Pointwise-≡↔≡ : Inverse (P.setoid A ×ₛ P.setoid B) (P.setoid (A × B))
Pointwise-≡↔≡ = record
  { to         = id
  ; from       = id
  ; to-cong    = ≡×≡⇒≡
  ; from-cong  = ≡⇒≡×≡
  ; inverse    = ≡×≡⇒≡ , ≡⇒≡×≡
  }
