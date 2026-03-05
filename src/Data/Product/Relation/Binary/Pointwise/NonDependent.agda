------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise products of binary relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Relation.Binary.Pointwise.NonDependent where

open import Data.Product.Base as Product using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Level using (Level; _⊔_; 0ℓ)
open import Function.Base using (id)
open import Function.Bundles using (Inverse)
open import Relation.Binary.Core using (REL; Rel; _⇒_)
open import Relation.Binary.Bundles
  using (Setoid; DecSetoid; Preorder; Poset; StrictPartialOrder)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as ≡
import Relation.Nullary.Decidable.Core as Dec using (_×?_)

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B C D : Set a
    R S ≈₁ ≈₂ : Rel A ℓ₁

------------------------------------------------------------------------
-- Definition

infixr 2 _×_

_×_ : REL A B ℓ₁ → REL C D ℓ₂ → REL (A Product.× C) (B Product.× D) (ℓ₁ ⊔ ℓ₂)
(R × S) (a , c) (b , d) = (R a b) Product.× (S c d)

------------------------------------------------------------------------
-- Pointwise preserves many relational properties

×-reflexive : ≈₁ ⇒ R → ≈₂ ⇒ S → (≈₁ × ≈₂) ⇒ (R × S)
×-reflexive refl₁ refl₂ = Product.map refl₁ refl₂

×-refl : Reflexive R → Reflexive S → Reflexive (R × S)
×-refl refl₁ refl₂ = refl₁ , refl₂

×-irreflexive₁ : Irreflexive ≈₁ R →
                 Irreflexive (≈₁ × ≈₂) (R × S)
×-irreflexive₁ ir x≈y x<y = ir (proj₁ x≈y) (proj₁ x<y)

×-irreflexive₂ : Irreflexive ≈₂ S →
                 Irreflexive (≈₁ × ≈₂) (R × S)
×-irreflexive₂ ir x≈y x<y = ir (proj₂ x≈y) (proj₂ x<y)

×-symmetric : Symmetric R → Symmetric S → Symmetric (R × S)
×-symmetric sym₁ sym₂ = Product.map sym₁ sym₂

×-transitive : Transitive R → Transitive S → Transitive (R × S)
×-transitive trans₁ trans₂ = Product.zip trans₁ trans₂

×-antisymmetric : Antisymmetric ≈₁ R → Antisymmetric ≈₂ S →
                  Antisymmetric (≈₁ × ≈₂) (R × S)
×-antisymmetric antisym₁ antisym₂ = Product.zip antisym₁ antisym₂

×-asymmetric₁ : Asymmetric R → Asymmetric (R × S)
×-asymmetric₁ asym₁ x<y y<x = asym₁ (proj₁ x<y) (proj₁ y<x)

×-asymmetric₂ : Asymmetric S → Asymmetric (R × S)
×-asymmetric₂ asym₂ x<y y<x = asym₂ (proj₂ x<y) (proj₂ y<x)

×-respectsʳ : R Respectsʳ ≈₁ → S Respectsʳ ≈₂ →
             (R × S) Respectsʳ (≈₁ × ≈₂)
×-respectsʳ resp₁ resp₂ = Product.zip resp₁ resp₂

×-respectsˡ : R Respectsˡ ≈₁ → S Respectsˡ ≈₂ →
             (R × S) Respectsˡ (≈₁ × ≈₂)
×-respectsˡ resp₁ resp₂ = Product.zip resp₁ resp₂

×-respects₂ : R Respects₂ ≈₁ → S Respects₂ ≈₂ →
              (R × S) Respects₂ (≈₁ × ≈₂)
×-respects₂ = Product.zip ×-respectsʳ ×-respectsˡ

×-total : Symmetric R → Total R → Total S → Total (R × S)
×-total sym₁ total₁ total₂ (x₁ , x₂) (y₁ , y₂)
  with total₁ x₁ y₁ | total₂ x₂ y₂
... | inj₁ x₁∼y₁ | inj₁ x₂∼y₂ = inj₁ (     x₁∼y₁ , x₂∼y₂)
... | inj₁ x₁∼y₁ | inj₂ y₂∼x₂ = inj₂ (sym₁ x₁∼y₁ , y₂∼x₂)
... | inj₂ y₁∼x₁ | inj₂ y₂∼x₂ = inj₂ (     y₁∼x₁ , y₂∼x₂)
... | inj₂ y₁∼x₁ | inj₁ x₂∼y₂ = inj₁ (sym₁ y₁∼x₁ , x₂∼y₂)

infixr 2 _×?_
_×?_ : Decidable R → Decidable S → Decidable (R × S)
_×?_ _R?_ _S?_ (x₁ , x₂) (y₁ , y₂) = (x₁ R? y₁) Dec.×? (x₂ S? y₂)

------------------------------------------------------------------------
-- Structures can also be combined.

-- Some collections of properties which are preserved by ×-Rel.

×-isEquivalence : IsEquivalence R → IsEquivalence S →
                  IsEquivalence (R × S)
×-isEquivalence {R = R} {S = S} eq₁ eq₂ = record
  { refl  = ×-refl {R = R} {S = S} (refl eq₁) (refl eq₂)
  ; sym   = ×-symmetric {R = R} {S = S} (sym eq₁) (sym eq₂)
  ; trans = ×-transitive {R = R} {S = S} (trans eq₁) (trans eq₂)
  } where open IsEquivalence

×-isDecEquivalence : IsDecEquivalence R → IsDecEquivalence S →
                     IsDecEquivalence (R × S)
×-isDecEquivalence eq₁ eq₂ = record
  { isEquivalence = ×-isEquivalence
                      (isEquivalence eq₁) (isEquivalence eq₂)
  ; _≟_           = (_≟_ eq₁) ×? (_≟_ eq₂)
  } where open IsDecEquivalence

×-isPreorder : IsPreorder ≈₁ R → IsPreorder ≈₂ S →
               IsPreorder (≈₁ × ≈₂) (R × S)
×-isPreorder {R = R} {S = S} pre₁ pre₂ = record
  { isEquivalence = ×-isEquivalence
                      (isEquivalence pre₁) (isEquivalence pre₂)
  ; reflexive     = ×-reflexive {R = R} {S = S}
                      (reflexive pre₁) (reflexive pre₂)
  ; trans         = ×-transitive {R = R} {S = S}
                      (trans pre₁) (trans pre₂)
  } where open IsPreorder

×-isPartialOrder : IsPartialOrder ≈₁ R → IsPartialOrder ≈₂ S →
                   IsPartialOrder (≈₁ × ≈₂) (R × S)
×-isPartialOrder {R = R} {S = S} po₁ po₂ = record
  { isPreorder = ×-isPreorder (isPreorder po₁) (isPreorder po₂)
  ; antisym    = ×-antisymmetric {R = R} {S = S}
                   (antisym po₁) (antisym po₂)
  } where open IsPartialOrder

×-isStrictPartialOrder : IsStrictPartialOrder ≈₁ R →
                         IsStrictPartialOrder ≈₂ S →
                         IsStrictPartialOrder (≈₁ × ≈₂) (R × S)
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

≡×≡⇒≡ : (_≡_ × _≡_) ⇒ _≡_ {A = A Product.× B}
≡×≡⇒≡ (≡.refl , ≡.refl) = ≡.refl

≡⇒≡×≡ : _≡_ {A = A Product.× B} ⇒ (_≡_ × _≡_)
≡⇒≡×≡ ≡.refl = ≡.refl , ≡.refl

×-≡↔≡-× : Inverse (≡.setoid A ×ₛ ≡.setoid B) (≡.setoid (A Product.× B))
×-≡↔≡-× = record
  { to         = id
  ; from       = id
  ; to-cong    = ≡×≡⇒≡
  ; from-cong  = ≡⇒≡×≡
  ; inverse    = ≡×≡⇒≡ , ≡⇒≡×≡
  }


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.4

Pointwise = _×_
{-# WARNING_ON_USAGE Pointwise
"Warning: Pointwise was deprecated in v2.4.
Please use _×_ instead."
#-}

×-decidable = _×?_
{-# WARNING_ON_USAGE ×-decidable
"Warning: ×-decidable was deprecated in v2.4.
Please use _×?_ instead."
#-}

Pointwise-≡↔≡ = ×-≡↔≡-×
{-# WARNING_ON_USAGE Pointwise-≡↔≡
"Warning: Pointwise-≡↔≡ was deprecated in v2.4.
Please use ×-≡↔≡-× instead."
#-}
