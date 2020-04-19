------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by total orders
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Properties.TotalOrder
  {t₁ t₂ t₃} (T : TotalOrder t₁ t₂ t₃) where

open TotalOrder T

open import Data.Sum.Base using (inj₁; inj₂)
import Relation.Binary.Construct.Converse as Converse
import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ as ToStrict
import Relation.Binary.Properties.Poset poset as PosetProperties
open import Relation.Binary.Consequences
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

------------------------------------------------------------------------
-- Total orders are almost decidable total orders

decTotalOrder : Decidable _≈_ → DecTotalOrder _ _ _
decTotalOrder ≟ = record
  { isDecTotalOrder = record
    { isTotalOrder = isTotalOrder
    ; _≟_          = ≟
    ; _≤?_         = total+dec⟶dec reflexive antisym total ≟
    }
  }

------------------------------------------------------------------------
-- _≥_ - the flipped relation is also a total order

open PosetProperties public
  using
  ( _≥_
  ; ≥-refl
  ; ≥-reflexive
  ; ≥-trans
  ; ≥-antisym
  ; ≥-isPreorder
  ; ≥-isPartialOrder
  ; ≥-preorder
  ; ≥-poset
  )

≥-isTotalOrder : IsTotalOrder _≈_ _≥_
≥-isTotalOrder = Converse.isTotalOrder isTotalOrder

≥-totalOrder : TotalOrder _ _ _
≥-totalOrder = record
  { isTotalOrder = ≥-isTotalOrder
  }

open TotalOrder ≥-totalOrder public
  using () renaming (total to ≥-total)

------------------------------------------------------------------------
-- _<_ - the strict version is a strict partial order

-- Note that total orders can NOT be turned into strict total orders as
-- in order to distinguish between the _≤_ and _<_ cases we must have
-- decidable equality _≈_.

open PosetProperties public
  using
  ( _<_
  ; <-resp-≈
  ; <-respʳ-≈
  ; <-respˡ-≈
  ; <-irrefl
  ; <-asym
  ; <-trans
  ; <-isStrictPartialOrder
  ; <-strictPartialOrder
  ; <⇒≉
  ; ≤∧≉⇒<
  ; <⇒≱
  ; ≤⇒≯
  )

≰⇒> : ∀ {x y} → ¬ (x ≤ y) → y < x
≰⇒> = ToStrict.≰⇒> Eq.sym reflexive total
