------------------------------------------------------------------------
-- The Agda standard library
--
-- The lifting of a non-strict order to incorporate a new infimum
------------------------------------------------------------------------

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Infimum

open import Relation.Binary

module Relation.Binary.Construct.Add.Infimum.NonStrict
  {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) where

open import Level
open import Data.Sum as Sum
import Relation.Binary.PropositionalEquality as P
import Relation.Binary.Construct.Add.Infimum.Equality as Equality
open import Relation.Nullary
open import Relation.Nullary.Construct.Add.Infimum
import Relation.Nullary.Decidable as Dec

------------------------------------------------------------------------
-- Definition

infix 5 _≤₋_
data _≤₋_ : Rel (A ₋) ℓ where
  ⊥₋≤_  : (l : A ₋)         → ⊥₋    ≤₋ l
  [_] : {k l : A} → k ≤ l → [ k ] ≤₋ [ l ]

------------------------------------------------------------------------
-- Relational properties

[≤]-injective : ∀ {k l} → [ k ] ≤₋ [ l ] → k ≤ l
[≤]-injective [ p ] = p

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  ≤₋-reflexive : (_≈_ ⇒ _≤_) → (_≈₋_ ⇒ _≤₋_)
  ≤₋-reflexive ≤-reflexive ⊥₋≈⊥₋ = ⊥₋≤ ⊥₋
  ≤₋-reflexive ≤-reflexive [ p ] = [ ≤-reflexive p ]

  ≤₋-antisym : Antisymmetric _≈_ _≤_ → Antisymmetric _≈₋_ _≤₋_
  ≤₋-antisym ≤≥⇒≈ (⊥₋≤ ⊥₋) (⊥₋≤ ⊥₋) = ⊥₋≈⊥₋
  ≤₋-antisym ≤≥⇒≈ [ p ] [ q ] = [ ≤≥⇒≈ p q ]

≤₋-trans : Transitive _≤_ → Transitive _≤₋_
≤₋-trans ≤-trans (⊥₋≤ l) q     = ⊥₋≤ _
≤₋-trans ≤-trans [ p ]   [ q ] = [ ≤-trans p q ]

≤₋-minimum : Minimum _≤₋_ ⊥₋
≤₋-minimum = ⊥₋≤_

≤₋-dec : Decidable _≤_ → Decidable _≤₋_
≤₋-dec _≤?_ ⊥₋    l     = yes (⊥₋≤ l)
≤₋-dec _≤?_ [ k ] ⊥₋    = no (λ ())
≤₋-dec _≤?_ [ k ] [ l ] = Dec.map′ [_] [≤]-injective (k ≤? l)

≤₋-total : Total _≤_ → Total _≤₋_
≤₋-total ≤-total ⊥₋    l     = inj₁ (⊥₋≤ l)
≤₋-total ≤-total k     ⊥₋    = inj₂ (⊥₋≤ k)
≤₋-total ≤-total [ k ] [ l ] = Sum.map [_] [_] (≤-total k l)

≤₋-irrelevant : Irrelevant _≤_ → Irrelevant _≤₋_
≤₋-irrelevant ≤-irr (⊥₋≤ k) (⊥₋≤ k) = P.refl
≤₋-irrelevant ≤-irr [ p ]   [ q ]   = P.cong _ (≤-irr p q)

------------------------------------------------------------------------
-- Structures

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  ≤₋-isPreorder : IsPreorder _≈_ _≤_ → IsPreorder _≈₋_ _≤₋_
  ≤₋-isPreorder ≤-isPreorder = record
    { isEquivalence = ≈₋-isEquivalence isEquivalence
    ; reflexive     = ≤₋-reflexive reflexive
    ; trans         = ≤₋-trans trans
    } where open IsPreorder ≤-isPreorder

  ≤₋-isPartialOrder : IsPartialOrder _≈_ _≤_ → IsPartialOrder _≈₋_ _≤₋_
  ≤₋-isPartialOrder ≤-isPartialOrder = record
    { isPreorder = ≤₋-isPreorder isPreorder
    ; antisym    = ≤₋-antisym antisym
    } where open IsPartialOrder ≤-isPartialOrder

  ≤₋-isDecPartialOrder : IsDecPartialOrder _≈_ _≤_ → IsDecPartialOrder _≈₋_ _≤₋_
  ≤₋-isDecPartialOrder ≤-isDecPartialOrder = record
    { isPartialOrder = ≤₋-isPartialOrder isPartialOrder
    ; _≟_            = ≈₋-dec _≟_
    ; _≤?_           = ≤₋-dec _≤?_
    } where open IsDecPartialOrder ≤-isDecPartialOrder

  ≤₋-isTotalOrder : IsTotalOrder _≈_ _≤_ → IsTotalOrder _≈₋_ _≤₋_
  ≤₋-isTotalOrder ≤-isTotalOrder = record
    { isPartialOrder = ≤₋-isPartialOrder isPartialOrder
    ; total          = ≤₋-total total
    } where open IsTotalOrder ≤-isTotalOrder

  ≤₋-isDecTotalOrder : IsDecTotalOrder _≈_ _≤_ → IsDecTotalOrder _≈₋_ _≤₋_
  ≤₋-isDecTotalOrder ≤-isDecTotalOrder = record
    { isTotalOrder = ≤₋-isTotalOrder isTotalOrder
    ; _≟_          = ≈₋-dec _≟_
    ; _≤?_         = ≤₋-dec _≤?_
    } where open IsDecTotalOrder ≤-isDecTotalOrder
