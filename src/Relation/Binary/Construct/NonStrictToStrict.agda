------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of _≤_ to _<_
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Construct.NonStrictToStrict
  {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; flip)
open import Relation.Nullary using (¬_; yes; no)

------------------------------------------------------------------------
-- _≤_ can be turned into _<_ as follows:

_<_ : Rel A _
x < y = (x ≤ y) × ¬ (x ≈ y)

------------------------------------------------------------------------
-- The converted relations have certain properties
-- (if the original relations have certain other properties)

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = proj₁

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
  (respˡ y≈z y≤x) , (λ z≈x → y≉x (trans y≈z z≈x))

<-respʳ-≈ : Symmetric _≈_ → Transitive _≈_ →
            _≤_ Respectsʳ _≈_ → _<_ Respectsʳ _≈_
<-respʳ-≈ sym trans respʳ {x} {y} {z} y≈z (x≤y , x≉y) =
  (respʳ y≈z x≤y) , λ x≈z → x≉y (trans x≈z (sym y≈z))

<-resp-≈ : IsEquivalence _≈_ → _≤_ Respects₂ _≈_ → _<_ Respects₂ _≈_
<-resp-≈ eq (respʳ , respˡ) =
  <-respʳ-≈ sym trans respʳ , <-respˡ-≈ trans respˡ
  where open IsEquivalence eq

<-trichotomous : Symmetric _≈_ → Decidable _≈_ →
                 Antisymmetric _≈_ _≤_ → Total _≤_ →
                 Trichotomous _≈_ _<_
<-trichotomous ≈-sym _≟_ antisym total x y with x ≟ y
... | yes x≈y = tri≈ (<-irrefl x≈y) x≈y (<-irrefl (≈-sym x≈y))
... | no  x≉y with total x y
...   | inj₁ x≤y = tri< (x≤y , x≉y) x≉y
                        (x≉y ∘ antisym x≤y ∘ proj₁)
...   | inj₂ x≥y = tri> (x≉y ∘ flip antisym x≥y ∘ proj₁) x≉y
                        (x≥y , x≉y ∘ ≈-sym)

<-decidable : Decidable _≈_ → Decidable _≤_ → Decidable _<_
<-decidable _≟_ _≤?_ x y with x ≟ y | x ≤? y
... | yes x≈y | _       = no (flip proj₂ x≈y)
... | no  x≉y | yes x≤y = yes (x≤y , x≉y)
... | no  x≉y | no  x≰y = no (x≰y ∘ proj₁)

<-isStrictPartialOrder : IsPartialOrder _≈_ _≤_ →
                         IsStrictPartialOrder _≈_ _<_
<-isStrictPartialOrder po = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans po
  ; <-resp-≈      = <-resp-≈ isEquivalence ≤-resp-≈
  } where open IsPartialOrder po

<-isStrictTotalOrder₁ : Decidable _≈_ → IsTotalOrder _≈_ _≤_ →
                        IsStrictTotalOrder _≈_ _<_
<-isStrictTotalOrder₁ ≟ tot = record
  { isEquivalence = isEquivalence
  ; trans         = <-trans isPartialOrder
  ; compare       = <-trichotomous Eq.sym ≟ antisym total
  } where open IsTotalOrder tot

<-isStrictTotalOrder₂ : IsDecTotalOrder _≈_ _≤_ →
                        IsStrictTotalOrder _≈_ _<_
<-isStrictTotalOrder₂ dtot = <-isStrictTotalOrder₁ _≟_ isTotalOrder
  where open IsDecTotalOrder dtot

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.16

irrefl         = <-irrefl
{-# WARNING_ON_USAGE irrefl
"Warning: irrefl was deprecated in v0.16.
Please use <-irrefl instead."
#-}
trans          = <-trans
{-# WARNING_ON_USAGE trans
"Warning: trans was deprecated in v0.16.
Please use <-trans instead."
#-}
antisym⟶asym = <-asym
{-# WARNING_ON_USAGE antisym⟶asym
"Warning: antisym⟶asym was deprecated in v0.16.
Please use <-asym instead."
#-}
decidable      = <-decidable
{-# WARNING_ON_USAGE decidable
"Warning: decidable was deprecated in v0.16.
Please use <-decidable instead."
#-}
trichotomous   = <-trichotomous
{-# WARNING_ON_USAGE trichotomous
"Warning: trichotomous was deprecated in v0.16.
Please use <-trichotomous instead."
#-}
isPartialOrder⟶isStrictPartialOrder = <-isStrictPartialOrder
{-# WARNING_ON_USAGE isPartialOrder⟶isStrictPartialOrder
"Warning: isPartialOrder⟶isStrictPartialOrder was deprecated in v0.16.
Please use <-isStrictPartialOrder instead."
#-}
isTotalOrder⟶isStrictTotalOrder     = <-isStrictTotalOrder₁
{-# WARNING_ON_USAGE isTotalOrder⟶isStrictTotalOrder
"Warning: isTotalOrder⟶isStrictTotalOrder was deprecated in v0.16.
Please use <-isStrictTotalOrder₁ instead."
#-}
isDecTotalOrder⟶isStrictTotalOrder  = <-isStrictTotalOrder₂
{-# WARNING_ON_USAGE isDecTotalOrder⟶isStrictTotalOrder
"Warning: isDecTotalOrder⟶isStrictTotalOrder was deprecated in v0.16.
Please use <-isStrictTotalOrder₂ instead."
#-}
