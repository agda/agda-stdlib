------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by total orders
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (TotalOrder; DecTotalOrder)

module Relation.Binary.Properties.TotalOrder
  {t₁ t₂ t₃} (T : TotalOrder t₁ t₂ t₃) where

open import Data.Product.Base using (proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
import Relation.Binary.Construct.Flip.EqAndOrd as EqAndOrd
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.Structures using (IsTotalOrder)
open import Relation.Binary.Consequences using (total∧dec⇒dec)

open TotalOrder T

import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ as ToStrict
import Relation.Binary.Properties.Poset poset as PosetProperties

------------------------------------------------------------------------
-- Total orders are almost decidable total orders

decTotalOrder : Decidable _≈_ → DecTotalOrder _ _ _
decTotalOrder ≟ = record
  { isDecTotalOrder = record
    { isTotalOrder = isTotalOrder
    ; _≟_          = ≟
    ; _≤?_         = total∧dec⇒dec reflexive antisym total ≟
    }
  }

------------------------------------------------------------------------
-- _≥_ - the flipped relation is also a total order

open PosetProperties public
  using
  ( ≥-refl
  ; ≥-reflexive
  ; ≥-trans
  ; ≥-antisym
  ; ≥-isPreorder
  ; ≥-isPartialOrder
  ; ≥-preorder
  ; ≥-poset
  )

≥-isTotalOrder : IsTotalOrder _≈_ _≥_
≥-isTotalOrder = EqAndOrd.isTotalOrder isTotalOrder

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

------------------------------------------------------------------------
-- _≰_ - the negated order

open PosetProperties public
  using
  ( ≰-respʳ-≈
  ; ≰-respˡ-≈
  )

≰⇒> : ∀ {x y} → x ≰ y → y < x
≰⇒> = ToStrict.≰⇒> Eq.sym reflexive total

≰⇒≥ : ∀ {x y} → x ≰ y → y ≤ x
≰⇒≥ x≰y = proj₁ (≰⇒> x≰y)
