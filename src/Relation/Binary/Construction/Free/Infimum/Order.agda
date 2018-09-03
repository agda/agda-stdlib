------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences on orders of freely adding an infimum to a Set
------------------------------------------------------------------------
open import Relation.Binary

module Relation.Binary.Construction.Free.Infimum.Order
       {a r} {A : Set a} (_≤_ : Rel A r) where

open import Level
open import Data.Sum as Sum
open import Function.Equivalence using (equivalence)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.Construction.Free.Infimum

infix 5 _≤₋_
data _≤₋_ : Rel (A ₋) r where
  ⊥⁺≤_  : (l : A ₋)         → ⊥⁺    ≤₋ l
  []≤[] : {k l : A} → k ≤ l → [ k ] ≤₋ [ l ]

[]≤[]⁻¹ : ∀ {k l} → [ k ] ≤₋ [ l ] → k ≤ l
[]≤[]⁻¹ ([]≤[] k≤l) = k≤l

module _ {e} {_≈_ : Rel A e} where

  open import Relation.Binary.Construction.Free.Infimum.Pointwise _≈_

  ≤₋-reflexive : (_≈_ ⇒ _≤_) → (_≈₋_ ⇒ _≤₋_)
  ≤₋-reflexive ≈⇒≤ ⊥⁺≈⊥⁺     = ⊥⁺≤ ⊥⁺
  ≤₋-reflexive ≈⇒≤ ([]≈[] p) = []≤[] (≈⇒≤ p)

  ≤₋-antisym : Antisymmetric _≈_ _≤_ → Antisymmetric _≈₋_ _≤₋_
  ≤₋-antisym ≤≥⇒≈ (⊥⁺≤ .⊥⁺) (⊥⁺≤ .⊥⁺) = ⊥⁺≈⊥⁺
  ≤₋-antisym ≤≥⇒≈ ([]≤[] p) ([]≤[] q) = []≈[] (≤≥⇒≈ p q)

≤₋-trans : Transitive _≤_ → Transitive _≤₋_
≤₋-trans ≤≤⇒≤ (⊥⁺≤ l)   q         = ⊥⁺≤ _
≤₋-trans ≤≤⇒≤ ([]≤[] p) ([]≤[] q) = []≤[] (≤≤⇒≤ p q)

≤₋-minimum : Minimum _≤₋_ ⊥⁺
≤₋-minimum = ⊥⁺≤_

≤₋-dec : Decidable _≤_ → Decidable _≤₋_
≤₋-dec ≤-dec ⊥⁺    l     = yes (⊥⁺≤ l)
≤₋-dec ≤-dec [ k ] ⊥⁺    = no (λ ())
≤₋-dec ≤-dec [ k ] [ l ] = Dec.map (equivalence []≤[] []≤[]⁻¹) (≤-dec k l)

≤₋-total : Total _≤_ → Total _≤₋_
≤₋-total ≤-total ⊥⁺    l     = inj₁ (⊥⁺≤ l)
≤₋-total ≤-total k     ⊥⁺    = inj₂ (⊥⁺≤ k)
≤₋-total ≤-total [ k ] [ l ] = Sum.map []≤[] []≤[] (≤-total k l)

module _ {e} {_≈_ : Rel A e} where

  open import Relation.Binary.Construction.Free.Infimum.Pointwise _≈_

  ≤₋-isPreorder : IsPreorder _≈_ _≤_ → IsPreorder _≈₋_ _≤₋_
  ≤₋-isPreorder pre = record
    { isEquivalence = ≈₋-isEquivalence isEquivalence
    ; reflexive     = λ {x} → ≤₋-reflexive reflexive {x}
    ; trans         = λ {x} → ≤₋-trans trans {x}
    } where open IsPreorder pre

  ≤₋-isPartialOrder : IsPartialOrder _≈_ _≤_ → IsPartialOrder _≈₋_ _≤₋_
  ≤₋-isPartialOrder part = record
    { isPreorder = ≤₋-isPreorder isPreorder
    ; antisym    = λ {x} → ≤₋-antisym antisym {x}
    } where open IsPartialOrder part

  ≤₋-isDecPartialOrder : IsDecPartialOrder _≈_ _≤_ → IsDecPartialOrder _≈₋_ _≤₋_
  ≤₋-isDecPartialOrder decpart = record
    { isPartialOrder = ≤₋-isPartialOrder isPartialOrder
    ; _≟_            = ≈₋-dec _≟_
    ; _≤?_           = ≤₋-dec _≤?_
    } where open IsDecPartialOrder decpart

  ≤₋-isTotalOrder : IsTotalOrder _≈_ _≤_ → IsTotalOrder _≈₋_ _≤₋_
  ≤₋-isTotalOrder tot = record
    { isPartialOrder = ≤₋-isPartialOrder isPartialOrder
    ; total          = ≤₋-total total
    } where open IsTotalOrder tot

  ≤₋-isDecTotalOrder : IsDecTotalOrder _≈_ _≤_ → IsDecTotalOrder _≈₋_ _≤₋_
  ≤₋-isDecTotalOrder dectot = record
    { isTotalOrder = ≤₋-isTotalOrder isTotalOrder
    ; _≟_          = ≈₋-dec _≟_
    ; _≤?_         = ≤₋-dec _≤?_
    } where open IsDecTotalOrder dectot
