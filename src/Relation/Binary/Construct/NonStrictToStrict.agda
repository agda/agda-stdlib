------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of _≤_ to _<_
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Relation.Binary.Construct.NonStrictToStrict
  {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) where

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (_∘_; flip)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (¬?; _×?_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Structures
  using (IsPartialOrder; IsEquivalence; IsStrictPartialOrder; IsDecPartialOrder
        ; IsDecStrictPartialOrder; IsTotalOrder; IsStrictTotalOrder
        ; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Trichotomous; Antisymmetric; Symmetric; Total; Decidable; Irreflexive
        ; Transitive; _Respectsʳ_; _Respectsˡ_; _Respects₂_; Trans; Asymmetric
        ; tri≈; tri<; tri>)

private
  _≉_ : Rel A ℓ₁
  x ≉ y = ¬ (x ≈ y)

------------------------------------------------------------------------
-- _≤_ can be turned into _<_ as follows:

infix 4  _<_

_<_ : Rel A _
x < y = x ≤ y × x ≉ y

------------------------------------------------------------------------
-- Relationship between relations

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = proj₁

<⇒≉ : ∀ {x y} → x < y → x ≉ y
<⇒≉ = proj₂

≤∧≉⇒< : ∀ {x y} → x ≤ y → x ≉ y → x < y
≤∧≉⇒< = _,_

<⇒≱ : Antisymmetric _≈_ _≤_ → ∀ {x y} → x < y → ¬ (y ≤ x)
<⇒≱ antisym (x≤y , x≉y) y≤x = x≉y (antisym x≤y y≤x)

≤⇒≯ : Antisymmetric _≈_ _≤_ → ∀ {x y} → x ≤ y → ¬ (y < x)
≤⇒≯ antisym x≤y y<x = <⇒≱ antisym y<x x≤y

≰⇒> : Symmetric _≈_ → (_≈_ ⇒ _≤_) → Total _≤_ →
      ∀ {x y} → ¬ (x ≤ y) → y < x
≰⇒> sym refl total {x} {y} x≰y with total x y
... | inj₁ x≤y = contradiction x≤y x≰y
... | inj₂ y≤x = y≤x , x≰y ∘ refl ∘ sym

≮⇒≥ : Symmetric _≈_ → Decidable _≈_ → _≈_ ⇒ _≤_ → Total _≤_ →
      ∀ {x y} → ¬ (x < y) → y ≤ x
≮⇒≥ sym _≈?_ ≤-refl _≤?_ {x} {y} x≮y with x ≈? y | y ≤? x
... | yes x≈y  | _        = ≤-refl (sym x≈y)
... | _        | inj₁ y≤x = y≤x
... | no  x≉y  | inj₂ x≤y = contradiction (x≤y , x≉y) x≮y

------------------------------------------------------------------------
-- Relational properties

<-irrefl : Irreflexive _≈_ _<_
<-irrefl x≈y (_ , x≉y) = x≉y x≈y

<-trans : IsPartialOrder _≈_ _≤_ → Transitive _<_
<-trans po (x≤y , x≉y) (y≤z , y≉z) =
  (trans x≤y y≤z , x≉y ∘ antisym x≤y ∘ trans y≤z ∘ reflexive ∘ Eq.sym)
  where open IsPartialOrder po

<-≤-trans : Symmetric _≈_ → Transitive _≤_ → Antisymmetric _≈_ _≤_ →
           _≤_ Respectsʳ _≈_ → Trans _<_ _≤_ _<_
<-≤-trans sym trans antisym respʳ (x≤y , x≉y) y≤z =
  trans x≤y y≤z , (λ x≈z → x≉y (antisym x≤y (respʳ (sym x≈z) y≤z)))

≤-<-trans : Transitive _≤_ → Antisymmetric _≈_ _≤_ →
           _≤_ Respectsˡ _≈_ → Trans _≤_ _<_ _<_
≤-<-trans trans antisym respʳ x≤y (y≤z , y≉z) =
  trans x≤y y≤z , (λ x≈z → y≉z (antisym y≤z (respʳ x≈z x≤y)))

<-asym : Antisymmetric _≈_ _≤_ → Asymmetric _<_
<-asym antisym (x≤y , x≉y) (y≤x , _) = x≉y (antisym x≤y y≤x)

<-respˡ-≈ : Transitive _≈_ → _≤_ Respectsˡ _≈_ → _<_ Respectsˡ _≈_
<-respˡ-≈ trans respˡ y≈z (y≤x , y≉x) =
  respˡ y≈z y≤x , y≉x ∘ trans y≈z

<-respʳ-≈ : Symmetric _≈_ → Transitive _≈_ →
            _≤_ Respectsʳ _≈_ → _<_ Respectsʳ _≈_
<-respʳ-≈ sym trans respʳ y≈z (x≤y , x≉y) =
  (respʳ y≈z x≤y) , λ x≈z → x≉y (trans x≈z (sym y≈z))

<-resp-≈ : IsEquivalence _≈_ → _≤_ Respects₂ _≈_ → _<_ Respects₂ _≈_
<-resp-≈ eq (respʳ , respˡ) =
  <-respʳ-≈ sym trans respʳ , <-respˡ-≈ trans respˡ
  where open IsEquivalence eq

<-trichotomous : Symmetric _≈_ → Decidable _≈_ →
                 Antisymmetric _≈_ _≤_ → Total _≤_ →
                 Trichotomous _≈_ _<_
<-trichotomous ≈-sym _≈?_ antisym total x y with x ≈? y
... | yes x≈y = tri≈ (<-irrefl x≈y) x≈y (<-irrefl (≈-sym x≈y))
... | no  x≉y with total x y
...   | inj₁ x≤y = tri< (x≤y , x≉y) x≉y (x≉y ∘ antisym x≤y ∘ proj₁)
...   | inj₂ y≤x = tri> (x≉y ∘ flip antisym y≤x ∘ proj₁) x≉y (y≤x , x≉y ∘ ≈-sym)

<-decidable : Decidable _≈_ → Decidable _≤_ → Decidable _<_
<-decidable _≈?_ _≤?_ x y = x ≤? y ×? ¬? (x ≈? y)

------------------------------------------------------------------------
-- Structures

<-isStrictPartialOrder : IsPartialOrder _≈_ _≤_ →
                         IsStrictPartialOrder _≈_ _<_
<-isStrictPartialOrder po = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans po
  ; <-resp-≈      = <-resp-≈ isEquivalence ≤-resp-≈
  } where open IsPartialOrder po

<-isDecStrictPartialOrder : IsDecPartialOrder _≈_ _≤_ →
                            IsDecStrictPartialOrder _≈_ _<_
<-isDecStrictPartialOrder dpo = record
  { isStrictPartialOrder = <-isStrictPartialOrder isPartialOrder
  ; _≈?_ = _≈?_
  ; _<?_ = <-decidable _≈?_ _≤?_
  } where open IsDecPartialOrder dpo

<-isStrictTotalOrder₁ : Decidable _≈_ → IsTotalOrder _≈_ _≤_ →
                        IsStrictTotalOrder _≈_ _<_
<-isStrictTotalOrder₁ ≈? tot = record
  { isStrictPartialOrder = <-isStrictPartialOrder isPartialOrder
  ; compare              = <-trichotomous Eq.sym ≈? antisym total
  } where open IsTotalOrder tot

<-isStrictTotalOrder₂ : IsDecTotalOrder _≈_ _≤_ →
                        IsStrictTotalOrder _≈_ _<_
<-isStrictTotalOrder₂ dtot = <-isStrictTotalOrder₁ _≈?_ isTotalOrder
  where open IsDecTotalOrder dtot
