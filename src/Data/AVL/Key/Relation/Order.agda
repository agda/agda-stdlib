------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of orders for keys for AVL trees.
------------------------------------------------------------------------

open import Relation.Binary

module Data.AVL.Key.Relation.Order
       {k r} (Key : Set k) (_≤_ : Rel Key r)
       where

open import Data.AVL.Key Key

open import Level
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum
open import Relation.Nullary

infix 4 _≤⁺_

_≤⁺_ : Key⁺ → Key⁺ → Set r
⊥⁺    ≤⁺ _     = Lift r ⊤
[ k ] ≤⁺ [ l ] = k ≤ l
_     ≤⁺ ⊤⁺    = Lift r ⊤
_     ≤⁺ _     = Lift r ⊥

module _ {e} {_≈_ : Rel Key e} where

  open import Data.AVL.Key.Relation.Pointwise Key _≈_

  ≤⁺-reflexive : (_≈_ ⇒ _≤_) → (_≈⁺_ ⇒ _≤⁺_)
  ≤⁺-reflexive ≈⇒≤ {⊥⁺}    {⊥⁺}    = _
  ≤⁺-reflexive ≈⇒≤ {⊤⁺}    {⊤⁺}    = _
  ≤⁺-reflexive ≈⇒≤ {[ k ]} {[ l ]} = ≈⇒≤
  -- impossible cases
  ≤⁺-reflexive ≈⇒≤ {⊥⁺} {⊤⁺} ()
  ≤⁺-reflexive ≈⇒≤ {⊥⁺} {[ _ ]} ()
  ≤⁺-reflexive ≈⇒≤ {⊤⁺} {⊥⁺} ()
  ≤⁺-reflexive ≈⇒≤ {⊤⁺} {[ _ ]} ()
  ≤⁺-reflexive ≈⇒≤ {[ _ ]} {⊥⁺} ()
  ≤⁺-reflexive ≈⇒≤ {[ _ ]} {⊤⁺} ()

  ≤⁺-antisym : Antisymmetric _≈_ _≤_ → Antisymmetric _≈⁺_ _≤⁺_
  ≤⁺-antisym ≤≥⇒≈ {⊥⁺}    {⊥⁺}    = _
  ≤⁺-antisym ≤≥⇒≈ {⊤⁺}    {⊤⁺}    = _
  ≤⁺-antisym ≤≥⇒≈ {[ k ]} {[ l ]} = ≤≥⇒≈
  -- impossible cases
  ≤⁺-antisym ≤≥⇒≈ {⊥⁺} {⊤⁺} k≤l ()
  ≤⁺-antisym ≤≥⇒≈ {⊥⁺} {[ k ]} k≤l ()
  ≤⁺-antisym ≤≥⇒≈ {⊤⁺} {⊥⁺} () k≥l
  ≤⁺-antisym ≤≥⇒≈ {⊤⁺} {[ k ]} () k≥l
  ≤⁺-antisym ≤≥⇒≈ {[ k ]} {⊥⁺} () k≥l
  ≤⁺-antisym ≤≥⇒≈ {[ k ]} {⊤⁺} k≤l ()

≤⁺-trans : Transitive _≤_ → Transitive _≤⁺_
≤⁺-trans ≤≤⇒≤ {⊥⁺}    {l}     {m}     = _
≤⁺-trans ≤≤⇒≤ {⊤⁺}    {⊤⁺}    {m}     = λ _ l≤m → l≤m
≤⁺-trans ≤≤⇒≤ {[ k ]} {⊤⁺}    {⊤⁺}    = _
≤⁺-trans ≤≤⇒≤ {[ k ]} {[ l ]} {⊤⁺}    = _
≤⁺-trans ≤≤⇒≤ {[ k ]} {[ l ]} {[ m ]} = ≤≤⇒≤
-- impossible cases
≤⁺-trans ≤≤⇒≤ {⊤⁺} {⊥⁺} {m} ()
≤⁺-trans ≤≤⇒≤ {⊤⁺} {[ k ]} {m} ()
≤⁺-trans ≤≤⇒≤ {[ k ]} {⊥⁺} {m} ()
≤⁺-trans ≤≤⇒≤ {[ k ]} {⊤⁺} {⊥⁺} _ ()
≤⁺-trans ≤≤⇒≤ {[ k ]} {⊤⁺} {[ l ]} _ ()
≤⁺-trans ≤≤⇒≤ {[ k ]} {[ l ]} {⊥⁺} _ ()

≤⁺-minimum : Minimum _≤⁺_ ⊥⁺
≤⁺-minimum = _

≤⁺-dec : Decidable _≤_ → Decidable _≤⁺_
≤⁺-dec ≤-dec ⊥⁺    l     = yes _
≤⁺-dec ≤-dec ⊤⁺    ⊤⁺    = yes _
≤⁺-dec ≤-dec [ k ] ⊤⁺    = yes _
≤⁺-dec ≤-dec [ k ] [ l ] = ≤-dec k l
-- impossible cases
≤⁺-dec ≤-dec ⊤⁺ ⊥⁺ = no λ ()
≤⁺-dec ≤-dec ⊤⁺ [ k ] = no λ ()
≤⁺-dec ≤-dec [ k ] ⊥⁺ = no λ ()

≤⁺-total : Total _≤_ → Total _≤⁺_
≤⁺-total ≤-total ⊥⁺    l     = inj₁ _
≤⁺-total ≤-total k     ⊥⁺    = inj₂ _
≤⁺-total ≤-total ⊤⁺    ⊤⁺    = inj₁ _
≤⁺-total ≤-total ⊤⁺    [ k ] = inj₂ _
≤⁺-total ≤-total [ k ] ⊤⁺    = inj₁ _
≤⁺-total ≤-total [ k ] [ l ] = ≤-total k l

module _ {e} {_≈_ : Rel Key e} where

  open import Data.AVL.Key.Relation.Pointwise Key _≈_

  ≤⁺-isPreorder : IsPreorder _≈_ _≤_ → IsPreorder _≈⁺_ _≤⁺_
  ≤⁺-isPreorder pre = record
    { isEquivalence = ≈⁺-isEquivalence isEquivalence
    ; reflexive     = λ {x} → ≤⁺-reflexive reflexive {x}
    ; trans         = λ {x} → ≤⁺-trans trans {x}
    } where open IsPreorder pre

  ≤⁺-isPartialOrder : IsPartialOrder _≈_ _≤_ → IsPartialOrder _≈⁺_ _≤⁺_
  ≤⁺-isPartialOrder part = record
    { isPreorder = ≤⁺-isPreorder isPreorder
    ; antisym    = λ {x} → ≤⁺-antisym antisym {x}
    } where open IsPartialOrder part

  ≤⁺-isDecPartialOrder : IsDecPartialOrder _≈_ _≤_ → IsDecPartialOrder _≈⁺_ _≤⁺_
  ≤⁺-isDecPartialOrder decpart = record
    { isPartialOrder = ≤⁺-isPartialOrder isPartialOrder
    ; _≟_            = ≈⁺-dec _≟_
    ; _≤?_           = ≤⁺-dec _≤?_
    } where open IsDecPartialOrder decpart

  ≤⁺-isTotalOrder : IsTotalOrder _≈_ _≤_ → IsTotalOrder _≈⁺_ _≤⁺_
  ≤⁺-isTotalOrder tot = record
    { isPartialOrder = ≤⁺-isPartialOrder isPartialOrder
    ; total          = ≤⁺-total total
    } where open IsTotalOrder tot

  ≤⁺-isDecTotalOrder : IsDecTotalOrder _≈_ _≤_ → IsDecTotalOrder _≈⁺_ _≤⁺_
  ≤⁺-isDecTotalOrder dectot = record
    { isTotalOrder = ≤⁺-isTotalOrder isTotalOrder
    ; _≟_          = ≈⁺-dec _≟_
    ; _≤?_         = ≤⁺-dec _≤?_
    } where open IsDecTotalOrder dectot
