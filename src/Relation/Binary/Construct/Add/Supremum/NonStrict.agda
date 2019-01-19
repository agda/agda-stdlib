------------------------------------------------------------------------
-- The Agda standard library
--
-- The lifting of a non-strict order to incorporate a new supremum
------------------------------------------------------------------------

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Supremum

open import Relation.Binary

module Relation.Binary.Construct.Add.Supremum.NonStrict
  {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) where

open import Level
open import Data.Sum as Sum
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary.Construct.Add.Supremum
import Relation.Binary.Construct.Add.Supremum.Equality as Equality

------------------------------------------------------------------------
-- Definition

data _≤⁺_ : Rel (A ⁺) ℓ where
  [_]  : {k l : A} → k ≤ l → [ k ] ≤⁺ [ l ]
  _≤⊤⁺ : (k : A ⁺)         → k     ≤⁺ ⊤⁺

------------------------------------------------------------------------
-- Properties

[≤]-injective : ∀ {k l} → [ k ] ≤⁺ [ l ] → k ≤ l
[≤]-injective [ p ] = p

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  ≤⁺-reflexive : (_≈_ ⇒ _≤_) → (_≈⁺_ ⇒ _≤⁺_)
  ≤⁺-reflexive ≤-reflexive [ p ] = [ ≤-reflexive p ]
  ≤⁺-reflexive ≤-reflexive ⊤⁺≈⊤⁺ = ⊤⁺ ≤⊤⁺

  ≤⁺-antisym : Antisymmetric _≈_ _≤_ → Antisymmetric _≈⁺_ _≤⁺_
  ≤⁺-antisym ≤-antisym [ p ]    [ q ]    = [ ≤-antisym p q ]
  ≤⁺-antisym ≤-antisym (⊤⁺ ≤⊤⁺) (⊤⁺ ≤⊤⁺) = ⊤⁺≈⊤⁺

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
≤⁺-irrelevant ≤-irr [ p ]   [ q ]    = P.cong _ (≤-irr p q)
≤⁺-irrelevant ≤-irr (k ≤⊤⁺) (k ≤⊤⁺) = P.refl

------------------------------------------------------------------------
-- Structures

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
