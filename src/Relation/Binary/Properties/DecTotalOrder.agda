------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by decidable total orders
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecTotalOrder; StrictTotalOrder)

module Relation.Binary.Properties.DecTotalOrder
  {d₁ d₂ d₃} (DTO : DecTotalOrder d₁ d₂ d₃) where

import Relation.Binary.Construct.Flip.EqAndOrd as EqAndOrd
  using (isDecTotalOrder)
open import Relation.Binary.Structures
  using (IsDecTotalOrder; IsStrictTotalOrder)
open import Relation.Nullary.Negation.Core using (¬_)

open DecTotalOrder DTO hiding (trans)

import Relation.Binary.Properties.TotalOrder totalOrder as TotalOrderProperties
import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ as ToStrict

------------------------------------------------------------------------
-- _≥_ - the flipped relation is also a total order

open TotalOrderProperties public
  using
  ( ≥-refl
  ; ≥-reflexive
  ; ≥-trans
  ; ≥-antisym
  ; ≥-total
  ; ≥-isPreorder
  ; ≥-isPartialOrder
  ; ≥-isTotalOrder
  ; ≥-preorder
  ; ≥-poset
  ; ≥-totalOrder
  )

≥-isDecTotalOrder : IsDecTotalOrder _≈_ _≥_
≥-isDecTotalOrder = EqAndOrd.isDecTotalOrder isDecTotalOrder

≥-decTotalOrder : DecTotalOrder _ _ _
≥-decTotalOrder = record
  { isDecTotalOrder = ≥-isDecTotalOrder
  }

open DecTotalOrder ≥-decTotalOrder public
  using () renaming (_≤?_ to _≥?_)

------------------------------------------------------------------------
-- _<_ - the strict version is a strict total order

open TotalOrderProperties public
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

<-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_
<-isStrictTotalOrder = ToStrict.<-isStrictTotalOrder₂ isDecTotalOrder

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  }

open StrictTotalOrder <-strictTotalOrder public
  using (_≮_) renaming (compare to <-compare)

------------------------------------------------------------------------
-- _≰_ - the negated order

open TotalOrderProperties public
  using
  ( ≰-respʳ-≈
  ; ≰-respˡ-≈
  ; ≰⇒>
  ; ≰⇒≥
  )

≮⇒≥ : ∀ {x y} → x ≮ y → y ≤ x
≮⇒≥ = ToStrict.≮⇒≥ Eq.sym _≟_ reflexive total

