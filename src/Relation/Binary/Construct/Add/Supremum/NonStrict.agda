------------------------------------------------------------------------
-- The Agda standard library
--
-- The lifting of a non-strict order to incorporate a new supremum
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Supremum

open import Relation.Binary.Core using (Rel; _⇒_)

module Relation.Binary.Construct.Add.Supremum.NonStrict
  {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) where

open import Level using (_⊔_)
open import Data.Product.Base as Product using (_,_)
open import Data.Sum.Base as Sum
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder; IsDecPartialOrder; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Maximum; Transitive; Total; Decidable; Irrelevant; Antisymmetric
        ; _Respectsˡ_; _Respectsʳ_; _Respects₂_)
import Relation.Nullary.Decidable.Core as Dec using (map′)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; subst)
import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Construct.Add.Supremum using (⊤⁺; _⁺; [_]; ≡-dec)
import Relation.Binary.Construct.Add.Supremum.Equality as Equality

------------------------------------------------------------------------
-- Definition

infix 4 _≤⁺_ _≤⊤⁺

data _≤⁺_ : Rel (A ⁺) (a ⊔ ℓ) where
  [_]  : {k l : A} → k ≤ l → [ k ] ≤⁺ [ l ]
  _≤⊤⁺ : (k : A ⁺)         → k     ≤⁺ ⊤⁺

------------------------------------------------------------------------
-- Properties

[≤]-injective : ∀ {k l} → [ k ] ≤⁺ [ l ] → k ≤ l
[≤]-injective [ p ] = p

≤⁺-trans : Transitive _≤_ → Transitive _≤⁺_
≤⁺-trans ≤-trans [ p ] [ q ]   = [ ≤-trans p q ]
≤⁺-trans ≤-trans p     (l ≤⊤⁺) = _ ≤⊤⁺

≤⁺-maximum : Maximum _≤⁺_ ⊤⁺
≤⁺-maximum = _≤⊤⁺

≤⁺-dec : Decidable _≤_ → Decidable _≤⁺_
≤⁺-dec _≤?_ k     ⊤⁺    = yes (k ≤⊤⁺)
≤⁺-dec _≤?_ ⊤⁺    [ l ] = no (λ ())
≤⁺-dec _≤?_ [ k ] [ l ] = Dec.map′ [_] [≤]-injective (k ≤? l)

≤⁺-total : Total _≤_ → Total _≤⁺_
≤⁺-total ≤-total k     ⊤⁺    = inj₁ (k ≤⊤⁺)
≤⁺-total ≤-total ⊤⁺    l     = inj₂ (l ≤⊤⁺)
≤⁺-total ≤-total [ k ] [ l ] = Sum.map [_] [_] (≤-total k l)

≤⁺-irrelevant : Irrelevant _≤_ → Irrelevant _≤⁺_
≤⁺-irrelevant ≤-irr [ p ]   [ q ]   = cong _ (≤-irr p q)
≤⁺-irrelevant ≤-irr (k ≤⊤⁺) (k ≤⊤⁺) = refl

------------------------------------------------------------------------
-- Relational properties + propositional equality

≤⁺-reflexive-≡ : (_≡_ ⇒ _≤_) → (_≡_ ⇒ _≤⁺_)
≤⁺-reflexive-≡ ≤-reflexive {[ x ]} refl = [ ≤-reflexive refl ]
≤⁺-reflexive-≡ ≤-reflexive {⊤⁺}    refl = ⊤⁺ ≤⊤⁺

≤⁺-antisym-≡ : Antisymmetric _≡_ _≤_ → Antisymmetric _≡_ _≤⁺_
≤⁺-antisym-≡ antisym (_ ≤⊤⁺) (_ ≤⊤⁺) = refl
≤⁺-antisym-≡ antisym [ p ] [ q ]     = cong [_] (antisym p q)

≤⁺-respˡ-≡ : _≤⁺_ Respectsˡ _≡_
≤⁺-respˡ-≡ = subst (_≤⁺ _)

≤⁺-respʳ-≡ : _≤⁺_ Respectsʳ _≡_
≤⁺-respʳ-≡ = subst (_ ≤⁺_)

≤⁺-resp-≡ : _≤⁺_ Respects₂ _≡_
≤⁺-resp-≡ = ≤⁺-respʳ-≡ , ≤⁺-respˡ-≡

------------------------------------------------------------------------
-- Relation properties + setoid equality

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  ≤⁺-reflexive : (_≈_ ⇒ _≤_) → (_≈⁺_ ⇒ _≤⁺_)
  ≤⁺-reflexive ≤-reflexive [ p ] = [ ≤-reflexive p ]
  ≤⁺-reflexive ≤-reflexive ⊤⁺≈⊤⁺ = ⊤⁺ ≤⊤⁺

  ≤⁺-antisym : Antisymmetric _≈_ _≤_ → Antisymmetric _≈⁺_ _≤⁺_
  ≤⁺-antisym ≤-antisym [ p ]    [ q ]  = [ ≤-antisym p q ]
  ≤⁺-antisym ≤-antisym (_ ≤⊤⁺) (_ ≤⊤⁺) = ⊤⁺≈⊤⁺

  ≤⁺-respˡ-≈⁺ : _≤_ Respectsˡ _≈_ → _≤⁺_ Respectsˡ _≈⁺_
  ≤⁺-respˡ-≈⁺ ≤-respˡ-≈ [ p ] [ q ] = [ ≤-respˡ-≈ p q ]
  ≤⁺-respˡ-≈⁺ ≤-respˡ-≈ [ p ] (l ≤⊤⁺) = [ _ ] ≤⊤⁺
  ≤⁺-respˡ-≈⁺ ≤-respˡ-≈ (⊤⁺≈⊤⁺) q = q

  ≤⁺-respʳ-≈⁺ : _≤_ Respectsʳ _≈_ → _≤⁺_ Respectsʳ _≈⁺_
  ≤⁺-respʳ-≈⁺ ≤-respʳ-≈ [ p ] [ q ] = [ ≤-respʳ-≈ p q ]
  ≤⁺-respʳ-≈⁺ ≤-respʳ-≈ ⊤⁺≈⊤⁺ q = q

  ≤⁺-resp-≈⁺ : _≤_ Respects₂ _≈_ → _≤⁺_ Respects₂ _≈⁺_
  ≤⁺-resp-≈⁺ = Product.map ≤⁺-respʳ-≈⁺ ≤⁺-respˡ-≈⁺

------------------------------------------------------------------------
-- Structures + propositional equality

≤⁺-isPreorder-≡ : IsPreorder _≡_ _≤_ → IsPreorder _≡_ _≤⁺_
≤⁺-isPreorder-≡ ≤-isPreorder = record
  { isEquivalence = ≡.isEquivalence
  ; reflexive     = ≤⁺-reflexive-≡ reflexive
  ; trans         = ≤⁺-trans trans
  } where open IsPreorder ≤-isPreorder

≤⁺-isPartialOrder-≡ : IsPartialOrder _≡_ _≤_ → IsPartialOrder _≡_ _≤⁺_
≤⁺-isPartialOrder-≡ ≤-isPartialOrder = record
  { isPreorder = ≤⁺-isPreorder-≡ isPreorder
  ; antisym    = ≤⁺-antisym-≡ antisym
  } where open IsPartialOrder ≤-isPartialOrder

≤⁺-isDecPartialOrder-≡ : IsDecPartialOrder _≡_ _≤_ → IsDecPartialOrder _≡_ _≤⁺_
≤⁺-isDecPartialOrder-≡ ≤-isDecPartialOrder = record
  { isPartialOrder = ≤⁺-isPartialOrder-≡ isPartialOrder
  ; _≟_            = ≡-dec _≟_
  ; _≤?_           = ≤⁺-dec _≤?_
  } where open IsDecPartialOrder ≤-isDecPartialOrder

≤⁺-isTotalOrder-≡ : IsTotalOrder _≡_ _≤_ → IsTotalOrder _≡_ _≤⁺_
≤⁺-isTotalOrder-≡ ≤-isTotalOrder = record
  { isPartialOrder = ≤⁺-isPartialOrder-≡ isPartialOrder
  ; total          = ≤⁺-total total
  } where open IsTotalOrder ≤-isTotalOrder

≤⁺-isDecTotalOrder-≡ : IsDecTotalOrder _≡_ _≤_ → IsDecTotalOrder _≡_ _≤⁺_
≤⁺-isDecTotalOrder-≡ ≤-isDecTotalOrder = record
  { isTotalOrder = ≤⁺-isTotalOrder-≡ isTotalOrder
  ; _≟_          = ≡-dec _≟_
  ; _≤?_         = ≤⁺-dec _≤?_
  } where open IsDecTotalOrder ≤-isDecTotalOrder

------------------------------------------------------------------------
-- Structures + setoid equality

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  ≤⁺-isPreorder : IsPreorder _≈_ _≤_ → IsPreorder _≈⁺_ _≤⁺_
  ≤⁺-isPreorder ≤-isPreorder = record
    { isEquivalence = ≈⁺-isEquivalence isEquivalence
    ; reflexive     = ≤⁺-reflexive reflexive
    ; trans         = ≤⁺-trans trans
    } where open IsPreorder ≤-isPreorder

  ≤⁺-isPartialOrder : IsPartialOrder _≈_ _≤_ → IsPartialOrder _≈⁺_ _≤⁺_
  ≤⁺-isPartialOrder ≤-isPartialOrder = record
    { isPreorder = ≤⁺-isPreorder isPreorder
    ; antisym    = ≤⁺-antisym antisym
    } where open IsPartialOrder ≤-isPartialOrder

  ≤⁺-isDecPartialOrder : IsDecPartialOrder _≈_ _≤_ → IsDecPartialOrder _≈⁺_ _≤⁺_
  ≤⁺-isDecPartialOrder ≤-isDecPartialOrder = record
    { isPartialOrder = ≤⁺-isPartialOrder isPartialOrder
    ; _≟_            = ≈⁺-dec _≟_
    ; _≤?_           = ≤⁺-dec _≤?_
    } where open IsDecPartialOrder ≤-isDecPartialOrder

  ≤⁺-isTotalOrder : IsTotalOrder _≈_ _≤_ → IsTotalOrder _≈⁺_ _≤⁺_
  ≤⁺-isTotalOrder ≤-isTotalOrder = record
    { isPartialOrder = ≤⁺-isPartialOrder isPartialOrder
    ; total          = ≤⁺-total total
    } where open IsTotalOrder ≤-isTotalOrder

  ≤⁺-isDecTotalOrder : IsDecTotalOrder _≈_ _≤_ → IsDecTotalOrder _≈⁺_ _≤⁺_
  ≤⁺-isDecTotalOrder ≤-isDecTotalOrder = record
    { isTotalOrder = ≤⁺-isTotalOrder isTotalOrder
    ; _≟_          = ≈⁺-dec _≟_
    ; _≤?_         = ≤⁺-dec _≤?_
    } where open IsDecTotalOrder ≤-isDecTotalOrder
