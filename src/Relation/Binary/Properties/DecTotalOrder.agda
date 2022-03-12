------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by decidable total orders
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Properties.DecTotalOrder
  {d₁ d₂ d₃} (DT : DecTotalOrder d₁ d₂ d₃) where

open DecTotalOrder DT hiding (trans)

import Relation.Binary.Construct.Converse as Converse
import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ as ToStrict
import Relation.Binary.Properties.TotalOrder totalOrder as TotalOrderProperties
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- _≥_ - the flipped relation is also a total order

open TotalOrderProperties public
  using
  ( _≥_
  ; ≥-refl
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
≥-isDecTotalOrder = Converse.isDecTotalOrder isDecTotalOrder

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
  using () renaming (compare to <-compare)

------------------------------------------------------------------------
-- _≰_ - the negated order

open TotalOrderProperties public
  using
  ( _≰_
  ; ≰-respʳ-≈
  ; ≰-respˡ-≈
  ; ≰⇒>
  ; ≰⇒≥
  )

≮⇒≥ : ∀ {x y} → ¬ (x < y) → y ≤ x
≮⇒≥ = ToStrict.≮⇒≥ Eq.sym _≟_ reflexive total
