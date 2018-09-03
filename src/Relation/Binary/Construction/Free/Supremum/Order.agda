------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences on orders of freely adding an infimum to a Set
------------------------------------------------------------------------
open import Relation.Binary

module Relation.Binary.Construction.Free.Supremum.Order
       {a r} {A : Set a} (_≤_ : Rel A r) where

open import Level
open import Data.Sum as Sum
open import Function.Equivalence using (equivalence)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.Construction.Free.Supremum

data _≤⁺_ : Rel (A ⁺) r where
  [_]  : {k l : A} → k ≤ l → [ k ] ≤⁺ [ l ]
  _≤⊤⁺ : (k : A ⁺)         → k     ≤⁺ ⊤⁺

[_]⁻¹ : ∀ {k l} → [ k ] ≤⁺ [ l ] → k ≤ l
[ [ p ] ]⁻¹ = p

module _ {e} {_≈_ : Rel A e} where

  open import Relation.Binary.Construction.Free.Supremum.Pointwise _≈_

  ≤⁺-reflexive : (_≈_ ⇒ _≤_) → (_≈⁺_ ⇒ _≤⁺_)
  ≤⁺-reflexive ≤-reflexive [ p ] = [ ≤-reflexive p ]
  ≤⁺-reflexive ≤-reflexive ⊤⁺≈⊤⁺ = ⊤⁺ ≤⊤⁺

  ≤⁺-antisym : Antisymmetric _≈_ _≤_ → Antisymmetric _≈⁺_ _≤⁺_
  ≤⁺-antisym ≤-antisym [ p ]     [ q ]     = [ ≤-antisym p q ]
  ≤⁺-antisym ≤-antisym (.⊤⁺ ≤⊤⁺) (.⊤⁺ ≤⊤⁺) = ⊤⁺≈⊤⁺

≤⁺-trans : Transitive _≤_ → Transitive _≤⁺_
≤⁺-trans ≤-trans [ p ] [ q ]   = [ ≤-trans p q ]
≤⁺-trans ≤-trans p     (l ≤⊤⁺) = _ ≤⊤⁺

≤⁺-maximum : Maximum _≤⁺_ ⊤⁺
≤⁺-maximum = _≤⊤⁺

≤⁺-dec : Decidable _≤_ → Decidable _≤⁺_
≤⁺-dec ≤-dec k     ⊤⁺    = yes (k ≤⊤⁺)
≤⁺-dec ≤-dec ⊤⁺    [ l ] = no (λ ())
≤⁺-dec ≤-dec [ k ] [ l ] = Dec.map (equivalence [_] [_]⁻¹) (≤-dec k l)

≤⁺-total : Total _≤_ → Total _≤⁺_
≤⁺-total ≤-total k     ⊤⁺    = inj₁ (k ≤⊤⁺)
≤⁺-total ≤-total ⊤⁺    l     = inj₂ (l ≤⊤⁺)
≤⁺-total ≤-total [ k ] [ l ] = Sum.map [_] [_] (≤-total k l)

module _ {e} {_≈_ : Rel A e} where

  open import Relation.Binary.Construction.Free.Supremum.Pointwise _≈_

  ≤⁺-isPreorder : IsPreorder _≈_ _≤_ → IsPreorder _≈⁺_ _≤⁺_
  ≤⁺-isPreorder ≤-isPreorder = record
    { isEquivalence = ≈⁺-isEquivalence isEquivalence
    ; reflexive     = λ {x} → ≤⁺-reflexive reflexive {x}
    ; trans         = λ {x} → ≤⁺-trans trans {x}
    } where open IsPreorder ≤-isPreorder

  ≤⁺-isPartialOrder : IsPartialOrder _≈_ _≤_ → IsPartialOrder _≈⁺_ _≤⁺_
  ≤⁺-isPartialOrder ≤-isPartialOrder = record
    { isPreorder = ≤⁺-isPreorder isPreorder
    ; antisym    = λ {x} → ≤⁺-antisym antisym {x}
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
