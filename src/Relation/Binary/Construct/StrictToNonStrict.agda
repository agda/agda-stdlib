------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of < to ≤, along with a number of properties
------------------------------------------------------------------------

-- Possible TODO: Prove that a conversion ≤ → < → ≤ returns a
-- relation equivalent to the original one (and similarly for
-- < → ≤ → <).

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Relation.Binary.Construct.StrictToNonStrict
  {a ℓ₁ ℓ₂} {A : Set a}
  (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂)
  where

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂; _⊎_; [_,_]; [_,_]′)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (_∘_; flip; _$_)
open import Relation.Binary.Consequences using (trans∧irr⇒asym)
open import Relation.Binary.Structures
  using (IsEquivalence; IsPreorder; IsStrictPartialOrder; IsPartialOrder
        ; IsStrictTotalOrder; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Transitive; Symmetric; Irreflexive; Antisymmetric; Trichotomous; Decidable
        ; Trans; Total; _Respects₂_; _Respectsʳ_; _Respectsˡ_; tri<; tri≈; tri>)
open import Relation.Nullary.Decidable.Core using (_⊎?_; yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)

------------------------------------------------------------------------
-- Conversion

-- _<_ can be turned into _≤_ as follows:
infix 4  _≤_

_≤_ : Rel A _
x ≤ y = (x < y) ⊎ (x ≈ y)

------------------------------------------------------------------------
-- The converted relations have certain properties
-- (if the original relations have certain other properties)

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = inj₁

reflexive : _≈_ ⇒ _≤_
reflexive = inj₂

antisym : IsEquivalence _≈_ → Transitive _<_ → Irreflexive _≈_ _<_ →
          Antisymmetric _≈_ _≤_
antisym eq trans irrefl = as
  where
  module Eq = IsEquivalence eq

  as : Antisymmetric _≈_ _≤_
  as (inj₂ x≈y) _          = x≈y
  as (inj₁ _)   (inj₂ y≈x) = Eq.sym y≈x
  as (inj₁ x<y) (inj₁ y<x) =
    contradiction y<x (trans∧irr⇒asym {_≈_ = _≈_} Eq.refl trans irrefl x<y)

trans : IsEquivalence _≈_ → _<_ Respects₂ _≈_ → Transitive _<_ →
        Transitive _≤_
trans eq (respʳ , respˡ) <-trans = tr
  where
  module Eq = IsEquivalence eq

  tr : Transitive _≤_
  tr (inj₁ x<y) (inj₁ y<z) = inj₁ $ <-trans x<y y<z
  tr (inj₁ x<y) (inj₂ y≈z) = inj₁ $ respʳ y≈z x<y
  tr (inj₂ x≈y) (inj₁ y<z) = inj₁ $ respˡ (Eq.sym x≈y) y<z
  tr (inj₂ x≈y) (inj₂ y≈z) = inj₂ $ Eq.trans x≈y y≈z

<-≤-trans : Transitive _<_ → _<_ Respectsʳ _≈_ → Trans _<_ _≤_ _<_
<-≤-trans trans respʳ x<y (inj₁ y<z) = trans x<y y<z
<-≤-trans trans respʳ x<y (inj₂ y≈z) = respʳ y≈z x<y

≤-<-trans : Symmetric _≈_ → Transitive _<_ → _<_ Respectsˡ _≈_ → Trans _≤_ _<_ _<_
≤-<-trans sym trans respˡ (inj₁ x<y) y<z = trans x<y y<z
≤-<-trans sym trans respˡ (inj₂ x≈y) y<z = respˡ (sym x≈y) y<z

≤-respʳ-≈ : Transitive _≈_ → _<_ Respectsʳ _≈_ → _≤_ Respectsʳ _≈_
≤-respʳ-≈ trans respʳ y′≈y (inj₁ x<y′) = inj₁ (respʳ y′≈y x<y′)
≤-respʳ-≈ trans respʳ y′≈y (inj₂ x≈y′) = inj₂ (trans x≈y′ y′≈y)

≤-respˡ-≈ : Symmetric _≈_ → Transitive _≈_ → _<_ Respectsˡ _≈_ → _≤_ Respectsˡ _≈_
≤-respˡ-≈ sym trans respˡ x′≈x (inj₁ x′<y) = inj₁ (respˡ x′≈x x′<y)
≤-respˡ-≈ sym trans respˡ x′≈x (inj₂ x′≈y) = inj₂ (trans (sym x′≈x) x′≈y)

≤-resp-≈ : IsEquivalence _≈_ → _<_ Respects₂ _≈_ → _≤_ Respects₂ _≈_
≤-resp-≈ eq (respʳ , respˡ) = ≤-respʳ-≈ Eq.trans respʳ , ≤-respˡ-≈ Eq.sym Eq.trans respˡ
  where module Eq = IsEquivalence eq

total : Trichotomous _≈_ _<_ → Total _≤_
total <-tri x y with <-tri x y
... | tri< x<y x≉y x≯y = inj₁ (inj₁ x<y)
... | tri≈ x≮y x≈y x≯y = inj₁ (inj₂ x≈y)
... | tri> x≮y x≉y x>y = inj₂ (inj₁ x>y)

decidable : Decidable _≈_ → Decidable _<_ → Decidable _≤_
decidable ≈-dec <-dec x y = <-dec x y ⊎? ≈-dec x y

decidable′ : Trichotomous _≈_ _<_ → Decidable _≤_
decidable′ compare x y with compare x y
... | tri< x<y _   _ = yes (inj₁ x<y)
... | tri≈ _   x≈y _ = yes (inj₂ x≈y)
... | tri> x≮y x≉y _ = no [ x≮y , x≉y ]′

------------------------------------------------------------------------
-- Converting structures

isPreorder₁ : IsPreorder _≈_ _<_ → IsPreorder _≈_ _≤_
isPreorder₁ PO = record
  { isEquivalence = S.isEquivalence
  ; reflexive     = reflexive
  ; trans         = trans S.isEquivalence S.∼-resp-≈ S.trans
  }
  where module S = IsPreorder PO

isPreorder₂ : IsStrictPartialOrder _≈_ _<_ → IsPreorder _≈_ _≤_
isPreorder₂ SPO = record
  { isEquivalence = S.isEquivalence
  ; reflexive     = reflexive
  ; trans         = trans S.isEquivalence S.<-resp-≈ S.trans
  }
  where module S = IsStrictPartialOrder SPO

isPartialOrder : IsStrictPartialOrder _≈_ _<_ → IsPartialOrder _≈_ _≤_
isPartialOrder SPO = record
  { isPreorder = isPreorder₂ SPO
  ; antisym    = antisym S.isEquivalence S.trans S.irrefl
  }
  where module S = IsStrictPartialOrder SPO

isTotalOrder : IsStrictTotalOrder _≈_ _<_ → IsTotalOrder _≈_ _≤_
isTotalOrder STO = record
  { isPartialOrder = isPartialOrder S.isStrictPartialOrder
  ; total          = total S.compare
  }
  where module S = IsStrictTotalOrder STO

isDecTotalOrder : IsStrictTotalOrder _≈_ _<_ → IsDecTotalOrder _≈_ _≤_
isDecTotalOrder STO = record
  { isTotalOrder = isTotalOrder STO
  ; _≟_          = S._≟_
  ; _≤?_         = decidable′ S.compare
  }
  where module S = IsStrictTotalOrder STO


------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.4

decidable' : Trichotomous _≈_ _<_ → Decidable _≤_
decidable' = decidable′
{-# WARNING_ON_USAGE decidable'
"Warning: decidable' (ending in an apostrophe) was deprecated in v1.4.
Please use decidable′ (ending in a prime) instead."
#-}
